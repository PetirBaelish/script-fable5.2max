-- @author 0x
-- @uid 0

-- ============================================================================
--  0x resolver  ·  v3.0  ·  unified build
--  Neverlose CS2 Lua  ·  API: github.com/PbLJk/neverlose-lua-api
--
--  This build merges three scripts into the resolver (s2) without renaming it:
--    s2  "0x resolver"        layered yaw/pitch resolver (the host, owns the menu)
--    s1  "0x · ragebot"       hitchance / min-damage / safepoint / body-aim assist
--    customresolver.lua       compact adaptive / jitter-spin / brute / static resolver
--
--  Credits: @kukluxk · @likvidatorchaes (subcult)
--
--  RESOLVER
--    1. per-netupdate yaw history   -> AA class (static / sway / jitter / spin / random)
--    2. pitch history               -> fake pitch class (down / up / zero / flicker)
--    3. body-yaw hint               -> model geometry from hitboxes (legs / shoulders)
--    4. freestanding hint           -> cover traces around the enemy head
--    5. movement memory + direction -> last movement yaw, side from movement direction
--    6. shot feedback               -> weapon_fire + player_hurt => hit / miss learning,
--                                      body-hit partial credit, anti-anti-bruteforce
--    7. bruteforce cycling          -> multiplier table or stepped offsets, locked on hit
--    8. persistence                 -> learned side per SteamID (db.*)
--  RAGEBOT ASSIST
--    Reads and writes your ragebot through config.get / config.set. Paths are discovered
--    from config.keys (group "Config link"); originals are journaled (db) and restored on
--    disable, pause, death, weapon change, map change, crash recovery and unload.
--    Air / apex hitchance, lethal body-aim via trace.damage, strict / body / damage binds,
--    and resolver-aware body-aim + hitchance for unresolved targets.
--  VISUALS
--    Player overlay, yaw lines, status panel (draggable while the menu is open),
--    event feed, debug panel.
--
--  m_angEyeAngles override requires "Allow Insecure". Without it the resolver runs in
--  tracking mode (overlay, stats, learning and the ragebot assist keep working).
-- ============================================================================

local META = {
    name        = "0x resolver",
    version     = "3.0",
    db          = "0x_resolver_v21",     -- learned sides, compatible with v2.1
    db_settings = "0x_s2_v3_settings",   -- menu snapshot
    db_journal  = "0x_v31_journal",      -- ragebot originals, compatible with s1 v3.x
    db_legacy   = "0x_v31_settings",     -- s1 settings, imported once when no v3 snapshot exists
    credits     = "@kukluxk · @likvidatorchaes (subcult)",
}

-- Manual config paths when auto-discovery picks the wrong ones. Example: hc = { "ragebot.hitchance" }
local CUSTOM_PATHS = { hc = {}, dmg = {}, safe = {}, baim = {}, hitbox = {} }
-- If safepoint in your ragebot is a dropdown, this is the index of the "Force" item.
local SAFE_COMBO_VALUE = 2

-- ----------------------------------------------------------------------------
-- Locals / fast paths
-- ----------------------------------------------------------------------------
local floor, abs, sqrt, atan2, sin, cos, rad, deg = math.floor, math.abs, math.sqrt, math.atan2, math.sin, math.cos, math.rad, math.deg
local max, min = math.max, math.min
local pcall, ipairs, pairs, type, tostring, tonumber, select, next = pcall, ipairs, pairs, type, tostring, tonumber, select, next
local format, s_lower, s_find, s_gsub, s_gmatch = string.format, string.lower, string.find, string.gsub, string.gmatch
local tremove, tconcat, tsort = table.remove, table.concat, table.sort
local band = bit.band

local normalize = math.normalize_angle or function(a) a = a % 360 if a > 180 then a = a - 360 end return a end
local clamp = math.clamp or function(v, lo, hi) if v < lo then return lo elseif v > hi then return hi end return v end
local calc_angle = math.calc_angle or function(from, to) return (to - from):angles() end
local lerp = math.lerp or function(a, b, t) return a + (b - a) * t end

local function safe(fn, ...)
    local ok, r = pcall(fn, ...)
    if ok then return r end
    return nil
end

local function sign(v)
    if v > 0 then return 1 elseif v < 0 then return -1 end
    return 0
end

local function round(v) return floor(v + 0.5) end

local function copy(v)
    if type(v) ~= "table" then return v end
    local o = {}
    for k, x in pairs(v) do o[k] = x end
    return o
end

local function same_scalar(a, b)
    if a == b then return true end
    if type(a) == "number" and type(b) == "number" then return abs(a - b) < 1e-4 end
    return false
end

local function same(a, b)
    if same_scalar(a, b) then return true end
    if type(a) ~= "table" or type(b) ~= "table" then return false end
    for k, v in pairs(a) do
        if not same_scalar(v, b[k]) then return false end
    end
    for k in pairs(b) do
        if a[k] == nil then return false end
    end
    return true
end

local function any_match(s, list)
    for i = 1, #list do
        if s_find(s, list[i]) then return true end
    end
    return false
end

local function utf8_len(s) return select(2, s_gsub(s, "[^\128-\193]", "")) end

local function say(msg) print("[0x] " .. tostring(msg)) end

-- ----------------------------------------------------------------------------
-- Constants
-- ----------------------------------------------------------------------------
local C = {                    -- resolver
    HISTORY          = 16,     -- yaw samples kept per player (~250 ms @ 64 tick)
    JITTER_MIN_DELTA = 12,     -- deg; a delta counts as "big" above this
    SPIN_MIN_RATE    = 20,     -- deg/update mean signed drift to classify as spin
    STATIC_MAX_DELTA = 3,      -- deg mean |delta| below this = static
    SWAY_MAX_DELTA   = 10,     -- deg mean |delta| below this (and not jitter) = sway
    RANDOM_CENTER_AT = 25,     -- deg mean |delta| above this -> circular mean as base
    MOVE_SPEED       = 4,      -- u/s 2D; above = moving
    MOVEDIR_SPEED    = 45,     -- u/s 2D; above = movement direction is a usable side hint
    MOVE_MEM_TIME    = 1.0,    -- s; movement memory validity after stopping
    BODY_MAX_DELTA   = 35,     -- deg; body hint saturates here
    BODY_MIN_DELTA   = 8,      -- deg; below = no hint
    BODY_SANE_DELTA  = 110,    -- deg; model yaw further than this from eye yaw = invalid sample
    FS_OFFSET        = 26,     -- u; lateral offset for freestanding traces
    FACE_ANGLE       = 35,     -- deg; eye yaw this close to "at target" = probably aiming, not AA
    FACE_SCALE       = 0.3,    -- desync multiplier while facing us
    SPIN_LEAD        = 0.5,    -- updates of spin extrapolation (Jitter / Spin mode)
    REVEAL_TIME      = 0.04,   -- s; skip samples right after the enemy fired (yaw snaps to his aim)
    SHOT_DEDUPE      = 0.10,   -- s; min interval between pending shots on the same target
    PURGE_AFTER      = 90,     -- s; drop records not seen for this long
    PENDING_MAX      = 32,     -- max outstanding shots
    DB_MAX           = 64,     -- persisted players
    FOCUS_FOV        = 15,     -- deg; crosshair target for panel / synergy
    W_LEARNED        = 1.00,
    W_BODY           = 0.55,
    W_FREESTAND      = 0.40,
    W_MOVE           = 0.30,
    W_MOVEDIR        = 0.30,
    SIDE_DEADZONE    = 0.15,
    HIT_CONF_GAIN    = 0.30,
    PARTIAL_GAIN     = 0.40,   -- share of HIT_CONF_GAIN for a body hit while aiming the head
    MISS_CONF_LOSS   = 0.20,
    ROUND_CONF_DECAY = 0.85,
    FEED_LIFE        = 5.0,    -- s; event feed line lifetime
    FEED_MAX         = 6,
}

local K = {                    -- ragebot assist
    EVAL_TICKS = 4,            -- target / lethality re-evaluation period, ticks
    VERIFY_TICKS = 16,         -- config cross-check period, ticks
    WEAPON_TICKS = 64,         -- weapon class re-check period, ticks
    HK_INTERVAL = 1.0,         -- housekeeping period, s
    SAVE_DELAY = 1.5,          -- autosave delay after the last menu change, s
    JOURNAL_LAZY = 15,         -- s of silence before stale journal entries are dropped from disk
    IO_RETRY = 5,              -- pause after a failed disk write, s
    CM_TIMEOUT = 0.5,          -- createmove silent longer than this -> ragebot values are restored, s
    PAINT_TIMEOUT = 2,         -- paint silent longer than this -> createmove runs background tasks, s
    MAX_CANDS = 48,            -- path candidates per parameter
    MAX_TARGETS = 3,           -- closest-to-crosshair targets to trace
    HOLD_TICKS = 12,           -- body-aim decision hold (anti flicker)
    MOVE_EPS = 5,              -- "moving" threshold, u/s
    T_MOVE_SQR = 1600,         -- target "running" above 40 u/s (squared)
    BAD_LIMIT = 3,             -- consecutive write failures before a path is disabled
    MISM_LIMIT = 3,            -- consecutive foreign overwrites before a path is disabled
    ERR_LIMIT = 25,            -- consecutive callback errors before suspension
    ERR_COOLDOWN = 5,          -- suspension length, s
    ERR_STRIKES = 3,           -- suspensions before a full stop
    ERR_FORGIVE = 60,          -- s without errors after which strikes are forgotten
    EYE_OFFSET = 46,           -- aim point height above the target origin
    HB_TTL = 256,              -- hitbox id cache lifetime, ticks
    HB_MAX = 64,
    GRAVITY = 800,
    SIM_MARGIN = 16,
    MEMO_MAX = 512,
    HG_HEAD = 1, HG_CHEST = 2, HG_STOMACH = 3,
    FL_DUCKING = 2,
    BTN_SPEED = (buttons and buttons.speed) or 65536,
}

local BRUTE = { 1.0, -1.0, 0.5, -0.5, 0.0, 0.75, -0.75 }   -- x max desync; index 1 is the trusted guess
local BRUTE_N = #BRUTE
local STEP_SEQ = { 0, 1, -1, 2, -2 }                        -- x brute step (customresolver pattern)
local STEP_N = #STEP_SEQ

local MODE_ADAPTIVE, MODE_STATIC, MODE_BRUTE, MODE_JITSPIN, MODE_OFFSET = 1, 2, 3, 4, 5
local BASE_AUTO, BASE_EYE, BASE_TARGET = 1, 2, 3
local PITCH_OFF, PITCH_CLAMP, PITCH_AUTO, PITCH_DOWN, PITCH_ZERO, PITCH_UP = 1, 2, 3, 4, 5, 6
local PAT_MULT, PAT_STEP = 1, 2

local STAGE_LAGCOMP = (stage and stage.lagcomp) or 6
local STAGE_NET_END = (stage and stage.net_update_end) or 7
local MASK_VISIBLE  = (trace and trace.mask and trace.mask.visible) or 1847299
local EYE_CLASSES   = { "C_CSPlayerPawn", "C_CSPlayerPawnBase", "CCSPlayerPawn" }
local MODE_LABEL    = { static = "STATIC", sway = "SWAY", jitter = "JITTER", spin = "SPIN", random = "RANDOM" }

local ST = { STAND = 1, SLOW = 2, MOVE = 3, DUCK = 4, AIR = 5, APEX = 6 }
local ST_NAME = { "STAND", "WALK", "RUN", "DUCK", "AIR", "APEX" }

local WPN_ITEMS = { "SSG 08", "AWP", "Auto snipers", "Deagle / R8", "Pistols", "Other" }
local WPN_BY_DEF = {
    [40] = 1, [9] = 2, [11] = 3, [38] = 3, [1] = 4, [64] = 4,
    [2] = 5, [3] = 5, [4] = 5, [30] = 5, [32] = 5, [36] = 5, [61] = 5, [63] = 5,
}
local WPN_BY_NAME = {
    { "ssg08", 1 }, { "awp", 2 }, { "g3sg1", 3 }, { "scar20", 3 }, { "deagle", 4 }, { "revolver", 4 },
    { "elite", 5 }, { "fiveseven", 5 }, { "glock", 5 }, { "tec9", 5 }, { "hkp2000", 5 },
    { "p250", 5 }, { "usp", 5 }, { "cz75", 5 },
}
local NON_GUN = {
    "knife", "bayonet", "grenade", "flashbang", "smoke", "molotov", "decoy", "c4", "taser",
    "healthshot", "fists", "melee", "axe", "hammer", "spanner", "tablet", "shield", "breach", "bump",
}
local NON_GUN_DEF = { [31] = true, [41] = true, [42] = true, [57] = true, [59] = true, [69] = true,
                      [70] = true, [72] = true, [74] = true, [75] = true, [76] = true, [78] = true, [85] = true }
for d = 43, 49 do NON_GUN_DEF[d] = true end
for d = 500, 526 do NON_GUN_DEF[d] = true end

-- ----------------------------------------------------------------------------
-- Shared runtime state
-- ----------------------------------------------------------------------------
local STATE = {
    now = 0, rt = 0,                       -- realtime snapshot for the current callback
    insecure = false,
    menu_open = false, menu_evt_t = -1e9, menu_poll_t = -1e9,
    cmd_angles = nil,                      -- angles actually sent (silent aim aware)
    lp_air = false, lp_moving = false,     -- local state for shot bookkeeping
    sw = 0, sh = 0,
    failed = false, suspend_until = nil, strikes = 0, strike_t = 0, errs = {},
    rep_last = nil, rep_t = -100,
    last_label = 0,
}

-- Module tables (filled in below). Keeping functions in tables keeps every closure far
-- below the 60-upvalue limit of LuaJIT.
local RES, RB, VIS, ACT = {}, {}, {}, {}
local Bind, Journal = {}, {}

local function report(where, err)
    local msg = tostring(err)
    if msg ~= STATE.rep_last or STATE.rt - STATE.rep_t > 5 then
        STATE.rep_last, STATE.rep_t = msg, STATE.rt
        say("error in " .. where .. ": " .. msg)
    end
end

-- ----------------------------------------------------------------------------
-- Menu: registry, constructors, snapshot
-- ----------------------------------------------------------------------------
local UI, REG, ORDER, CFG = {}, {}, {}, {}
local MENU = { combo_base = nil, last = -1e9, built = false }
local SET = { dirty = false, dirty_t = 0, io_t = -1e9 }
local PS = { last = nil, sync = true, applying = false }

-- A failed element must not take the script down: it is replaced by an inert stand-in.
local function dummy_el(def)
    local d = { dummy = true }
    d.get = function() return def end
    d.set = function() end
    d.depends = function() return d end
    d.tooltip = function() return d end
    d.visible = function() return d end
    d.active = function() return false end
    return d
end

local function create(g, ctor, id, def, ...)
    local ok, el = pcall(ctor, g, ...)
    if not ok or not el then
        say("menu element '" .. tostring(id) .. "' not created: " .. tostring(el))
        el = dummy_el(def)
    end
    return el
end

local function reg(id, kind, el, def, lo, hi, items, tip)
    REG[id] = { id = id, kind = kind, el = el, def = def, lo = lo, hi = hi, items = items }
    ORDER[#ORDER + 1] = id
    UI[id] = el
    if tip and not el.dummy then pcall(el.tooltip, el, tip) end
    return el
end

local function set_combo(el, items, idx1)
    if el.dummy then return end
    local v = safe(el.get, el)
    if type(v) == "string" then
        pcall(el.set, el, items[idx1])
    else
        pcall(el.set, el, (MENU.combo_base or 0) + idx1 - 1)
    end
end

local function combo_index(el, items)
    local v = safe(el.get, el)
    if type(v) == "number" then
        return clamp(floor(v + 0.5) - (MENU.combo_base or 0) + 1, 1, #items)
    elseif type(v) == "string" then
        for i = 1, #items do
            if items[i] == v then return i end
        end
    end
    return nil
end

local function chk(g, id, name, def, tip)
    return reg(id, "check", create(g, g.checkbox, id, def, name, def), def, nil, nil, nil, tip)
end

local function sld(g, id, name, lo, hi, def, fmt, tip)
    return reg(id, "slider", create(g, g.slider_int, id, def, name, lo, hi, def, fmt or "%d"), def, lo, hi, nil, tip)
end

-- Combo items are 1-based everywhere in this script; the widget base (0 or 1) is detected once.
local function cmb(g, id, name, items, def1, tip)
    local el = create(g, g.combo, id, def1, name, items)
    if not el.dummy then
        local v = safe(el.get, el)
        if MENU.combo_base == nil and type(v) == "number" then
            MENU.combo_base = (v == 0) and 0 or 1
        end
        if def1 > 1 then set_combo(el, items, def1) end
    end
    return reg(id, "combo", el, def1, 1, #items, items, tip)
end

local function clr(g, id, name, def, tip)
    return reg(id, "color", create(g, g.color, id, def, name, def, true), def, nil, nil, nil, tip)
end

local function key(g, id, name, tip)
    return reg(id, "key", create(g, g.keybind, id, false, name, 0), false, nil, nil, nil, tip)
end

local function mcb(g, id, name, items, defs, tip)
    return reg(id, "multi", create(g, g.multi_combo, id, defs, name, items, defs), defs, nil, nil, items, tip)
end

local function lbl(g, text)
    return create(g, g.label, "label", nil, text)
end

local function btn(g, id, name, act, tip)
    local el = create(g, g.button, id, nil, name, function()
        local f = ACT[act]
        if not f then return end
        STATE.rt = globals.realtime()
        local ok, err = pcall(f)
        if not ok then report("button " .. act, err) end
    end)
    if tip and not el.dummy then pcall(el.tooltip, el, tip) end
    return el
end

local function div(g, text) pcall(g.divider, g, text) end

local function dep(el, other)
    if el.dummy or other.dummy then return el end
    pcall(el.depends, el, other)
    return el
end

-- multi_combo value may arrive as {[name]=bool}, {bool,...} or a list of selected names / indices.
local function multi_on(v, idx, items)
    if type(v) ~= "table" then return false end
    local name = items[idx]
    local x = v[name]
    if x ~= nil then return x == true end
    x = v[idx]
    if type(x) == "boolean" then return x end
    for i = 1, #v do
        local e = v[i]
        if e == name or e == idx or e == idx - 1 then return true end
    end
    return false
end

local function bind_on(el)
    if el == nil or el.dummy then return false end
    local ok, v = pcall(el.active, el)
    return ok and v == true
end

local MODE_ITEMS    = { "Adaptive", "Static side", "Bruteforce", "Jitter / Spin", "Static offset" }
local BASE_ITEMS    = { "Auto", "Eye yaw", "At target" }
local PITCH_ITEMS   = { "Off", "Clamp", "Auto", "Force down", "Force zero", "Force up" }
local BRUTE_ITEMS   = { "Multipliers", "Stepped" }
local OVERLAY_ITEMS = { "Compact", "Detailed" }
local PRESET_ITEMS  = { "Custom", "Balanced", "Aggressive", "Conservative" }
local AIR_ITEMS     = { "Ground + vertical speed", "Ground flag only", "Landing prediction" }

local PRESETS = {
    [2] = { name = "Balanced", air_hc = 70, apex_hc = 58, air_dmg = 50, hc_stand = 70, hc_slow = 65, hc_move = 55,
            hc_duck = 72, hc_tgt_air = -8, hc_tgt_move = 0, strict_bonus = 12, baim_margin = 2,
            baim_lethal = true, baim_2x = false, dmg_cap = true },
    [3] = { name = "Aggressive", air_hc = 58, apex_hc = 48, air_dmg = 38, hc_stand = 60, hc_slow = 55, hc_move = 45,
            hc_duck = 62, hc_tgt_air = -12, hc_tgt_move = -4, strict_bonus = 8, baim_margin = 0,
            baim_lethal = true, baim_2x = true, dmg_cap = true },
    [4] = { name = "Conservative", air_hc = 78, apex_hc = 68, air_dmg = 62, hc_stand = 80, hc_slow = 75, hc_move = 66,
            hc_duck = 82, hc_tgt_air = -4, hc_tgt_move = 0, strict_bonus = 16, baim_margin = 5,
            baim_lethal = true, baim_2x = false, dmg_cap = true },
}

-- A tab or group that fails to build becomes an empty table: every constructor then falls
-- through create() into an inert stand-in and the script keeps running with defaults.
local function mk_tab(name)
    local ok, t = pcall(ui.tab, name)
    if not ok or not t then
        say("tab '" .. name .. "' not created: " .. tostring(t))
        return {}
    end
    return t
end

local function mk_group(tab, name)
    local ok, g = pcall(tab.group, tab, name)
    if not ok or not g then
        say("group '" .. name .. "' not created: " .. tostring(g))
        return {}
    end
    return g
end

local function build_menu()
    -- ---------------------------------------------------------------- tab 1
    local tab = mk_tab("0x Resolver")

    local g = mk_group(tab, "Resolver")
    local enable = chk(g, "enable", "Enable resolver", true, "Master switch of the resolver. The ragebot assist has its own switch on the 0x Ragebot tab.")
    dep(chk(g, "apply", "Override eye angles", true, "Writes the resolved angles into m_angEyeAngles every net update.\nRequires Allow Insecure; without it the resolver only tracks."), enable)
    dep(cmb(g, "mode", "Mode", MODE_ITEMS, MODE_ADAPTIVE,
        "Adaptive: all hints + learning + brute cycling.\nStatic side: learned side only.\nBruteforce: cycle the pattern on misses.\nJitter / Spin: jitter -> center, spin -> extrapolated yaw.\nStatic offset: yaw relative to you (Yaw offset)."), enable)
    dep(sld(g, "desync", "Max desync", 0, 90, 58, "%d°", "Desync amount applied to the base yaw."), enable)
    dep(sld(g, "yaw_off", "Yaw offset", -180, 180, 0, "%d°", "Static offset mode: resolved yaw = (yaw towards you) + offset."), enable)
    dep(cmb(g, "brute_pat", "Brute pattern", BRUTE_ITEMS, PAT_MULT, "Multipliers: 1, -1, 0.5, -0.5, 0, 0.75, -0.75 x max desync.\nStepped: 0, +1, -1, +2, -2 x brute step."), enable)
    dep(sld(g, "brute_step", "Brute step", 5, 90, 30, "%d°", "Step of the Stepped pattern."), enable)
    dep(cmb(g, "base", "Yaw base", BASE_ITEMS, BASE_AUTO, "Auto: spin -> at target, jitter -> center, otherwise eye yaw."), enable)
    dep(cmb(g, "pitch", "Pitch", PITCH_ITEMS, PITCH_AUTO, "Auto resolves fake pitch flicker to down and clamps the rest."), enable)
    dep(sld(g, "move_sc", "Moving correction", 0, 100, 35, "%d%%", "Share of the desync applied while the enemy moves."), enable)
    dep(sld(g, "jit_sc", "Jitter correction", 0, 100, 50, "%d%%", "Share of the desync applied on top of the jitter center."), enable)
    dep(chk(g, "face_damp", "Facing-target damping", true, "An eye yaw within 35° of you usually means he is aiming, not anti-aiming: desync is scaled down."), enable)

    local gi = mk_group(tab, "Intelligence")
    dep(chk(gi, "body", "Body yaw hint", true, "Estimates lower/upper body yaw from hitbox geometry."), enable)
    dep(chk(gi, "freestand", "Freestanding hint", true, "Traces cover left/right of the head; freestanding AA hides toward cover."), enable)
    dep(chk(gi, "move_mem", "Movement memory", true, "Remembers the last movement yaw for a second after the enemy stops."), enable)
    dep(chk(gi, "move_dir", "Side from movement direction", true, "While running, the side is hinted by the movement direction relative to you."), enable)
    local feedback = dep(chk(gi, "feedback", "Hit / miss learning", true, "weapon_fire + player_hurt feedback drives side confidence and brute cycling."), enable)
    dep(sld(gi, "miss_win", "Miss window", 150, 1000, 350, "%d ms", "A shot without player_hurt within this window counts as a miss."), feedback)
    dep(sld(gi, "miss_tol", "Misses before step", 1, 3, 1, nil, "Consecutive misses on a standing target before the brute index steps."), feedback)
    dep(chk(gi, "body_partial", "Body hit = partial", true, "A body hit while the ragebot was not forcing body-aim gives reduced confidence and does not lock the brute index."), feedback)
    dep(chk(gi, "anti_ab", "Detect anti-bruteforce", true, "If the target flips his side after every hit, the next prediction flips with him."), feedback)
    dep(chk(gi, "flip_on_hurt", "Flip side when they hit you", false, "customresolver behaviour: invert the learned side of an enemy who just hit you."), feedback)
    dep(chk(gi, "persist", "Persist learning (db)", true, "Keeps learned sides per SteamID between sessions."), feedback)

    local gv = mk_group(tab, "Visuals")
    dep(chk(gv, "overlay", "Player overlay", true, "AA class, side and desync above every tracked enemy."), enable)
    dep(cmb(gv, "ov_style", "Overlay style", OVERLAY_ITEMS, 1, "Detailed adds confidence bar, hits / misses, brute index and pitch class."), enable)
    dep(chk(gv, "yaw_lines", "Yaw lines", true, "Short lines from the head: dim = received yaw, accent = resolved yaw."), enable)
    chk(gv, "panel", "Status panel", true, "Panel with movement state, live ragebot overrides and the crosshair target's AA.\nDrag it with the mouse while the menu is open.")
    sld(gv, "panel_x", "Panel X", 0, 100, 1, "%d%%")
    sld(gv, "panel_y", "Panel Y", 0, 100, 40, "%d%%")
    sld(gv, "panel_scale", "Panel scale", 80, 150, 100, "%d%%")
    chk(gv, "feed", "Event feed", true, "Hit / miss / brute events under the panel.")
    clr(gv, "accent", "Accent color", color(140, 148, 255, 255), "Overlay, lines and panel accent.")
    chk(gv, "debug", "Debug panel", false, "Per-record internals and module state.")

    local gd = mk_group(tab, "Data")
    UI.stats = lbl(gd, "tracked 0 · hits 0 · misses 0")
    lbl(gd, "by 0x · " .. META.credits)
    chk(gd, "notif", "Notifications", true)
    chk(gd, "persist_ui", "Remember settings (db)", true, "Stores this menu in data\\db and restores it on load.")
    btn(gd, "reset_learn", "Clear learned data", "reset_learn", "Forget every learned side and the hit / miss statistics.")
    btn(gd, "reset_ui", "Reset settings to defaults", "reset_ui")

    -- ---------------------------------------------------------------- tab 2
    local rtab = mk_tab("0x Ragebot")

    local gm = mk_group(rtab, "Ragebot assist")
    local rb = chk(gm, "rb_enable", "Enable ragebot assist", true, "Drives hitchance, min damage, safepoint and hitboxes of your ragebot through config paths.\nEverything is restored on pause, death, weapon change and unload.")
    dep(cmb(gm, "preset", "Preset", PRESET_ITEMS, 2, "Balanced is universal, Aggressive fires sooner, Conservative wants more certainty.\nEditing a value switches the preset to Custom."), rb)
    dep(chk(gm, "pause_menu", "Pause while menu is open", true, "Your values are restored while the Neverlose menu is open so you can edit the ragebot freely."), rb)
    dep(mcb(gm, "weapons", "Weapon groups", WPN_ITEMS, { true, true, true, true, true, false }, "The assist only touches the ragebot while one of the selected groups is active."), rb)
    dep(chk(gm, "log_cfg", "Log config writes", false, "Prints path, old and new value of every config write to the Lua console."), rb)

    local gb = mk_group(rtab, "Binds")
    key(gb, "k_strict", "Strict · max accuracy", "While held: hitchance + Strict bonus, safepoint forced.")
    dep(sld(gb, "strict_bonus", "Strict hitchance bonus", 0, 40, 12, "+%d%%"), rb)
    key(gb, "k_baim", "Force body-aim", "While held: head is removed from the hitboxes.")
    key(gb, "k_dmg", "Min damage override", "While held: min damage = the value below.")
    dep(sld(gb, "dmg_bind_val", "Override min damage", 1, 130, 30, "%d HP"), rb)

    local ga = mk_group(rtab, "Air")
    local air = dep(chk(ga, "air_on", "Jump optimizer", true, "Air hitchance, min damage and safepoint while you are airborne.\nSSG 08 reference: hitchance 65-78, damage 45-65."), rb)
    dep(sld(ga, "air_hc", "Air hitchance", 1, 100, 70, "%d%%"), air)
    dep(sld(ga, "air_dmg", "Air min damage", 1, 130, 50, "%d HP"), air)
    dep(chk(ga, "air_safe", "Air safepoint", true), air)
    div(ga, "Apex")
    local apex = dep(chk(ga, "apex_on", "Apex hitchance", true, "At the top of the jump the vertical speed is near zero and spread is minimal."), air)
    dep(sld(ga, "apex_hc", "Apex hitchance", 1, 100, 58, "%d%%"), apex)
    dep(sld(ga, "apex_win", "Apex window", 10, 110, 42, "≤ %d u/s", "Apex while |vertical speed| is below this."), apex)
    div(ga, "Detection")
    dep(cmb(ga, "air_mode", "Air detection", AIR_ITEMS, 1, "Ground + vertical speed ignores stairs. Ground flag only reacts fastest.\nLanding prediction restores ground values a few ticks before touchdown (engine.simulate)."), rb)
    dep(sld(ga, "air_thr", "Vertical speed threshold", 5, 220, 22, "%d u/s"), rb)
    dep(sld(ga, "land_ticks", "Landing lead", 1, 8, 3, "%d ticks"), rb)

    local gc = mk_group(rtab, "Accuracy")
    local hc_on = dep(chk(gc, "hc_on", "Hitchance by state", true, "Own hitchance for standing, walking, running and ducking. 0 keeps yours."), rb)
    dep(sld(gc, "hc_stand", "Standing", 0, 100, 70, "%d%%"), hc_on)
    dep(sld(gc, "hc_slow", "Walking", 0, 100, 65, "%d%%"), hc_on)
    dep(sld(gc, "hc_move", "Running", 0, 100, 55, "%d%%"), hc_on)
    dep(sld(gc, "hc_duck", "Ducking", 0, 100, 72, "%d%%"), hc_on)
    div(gc, "Target")
    dep(sld(gc, "baim_fov", "Target search FOV", 5, 180, 60, "%d°", "Angle around the crosshair in which the target for corrections, damage cap and body-aim is searched."), rb)
    dep(sld(gc, "hc_tgt_air", "Target in air", -30, 30, -8, "%+d%%"), rb)
    dep(sld(gc, "hc_tgt_move", "Target running", -30, 30, 0, "%+d%%"), rb)
    dep(sld(gc, "unres_hc", "Target unresolved", -30, 30, 8, "%+d%%", "Hitchance adjustment when the resolver has little trust in its guess for the target."), rb)
    dep(chk(gc, "dmg_cap", "Cap min damage at target HP", true, "A finishing shot is never blocked by a min damage above the target's HP."), rb)

    local gba = mk_group(rtab, "Body-aim")
    local baim = dep(chk(gba, "baim_on", "Smart body-aim", true, "Body damage is traced; the head is removed from the hitboxes when the body is the better target."), rb)
    dep(chk(gba, "baim_lethal", "Body kills in 1 shot", true), baim)
    dep(chk(gba, "baim_2x", "Body kills in 2 shots", false, "Two body hits kill while one head hit would not (Deagle, pistols)."), baim)
    dep(sld(gba, "baim_margin", "Damage margin", 0, 30, 2, "%d HP"), baim)
    dep(chk(gba, "baim_hp_on", "Body at low HP", false), baim)
    dep(sld(gba, "baim_hp", "HP threshold", 1, 100, 40, "%d HP"), baim)
    dep(chk(gba, "baim_unres", "Body when unresolved", true, "Resolver synergy: random / wide jitter targets with low confidence, repeated misses or a deep brute index get body-aim (reason RES)."), baim)

    local gl = mk_group(rtab, "Config link")
    UI.rb_status = lbl(gl, "Paths: scanning…")
    btn(gl, "rescan", "Rescan config", "rescan", "Find the ragebot paths in config.keys again.")
    btn(gl, "dump", "Dump paths to console", "dump", "Prints the discovered paths with their current values.")

    MENU.built = true
end

-- ---------------------------------------------------------------- snapshot
local function read(r)
    local el = r.el
    local ok, v = pcall(el.get, el)
    if not ok or v == nil then
        if CFG[r.id] ~= nil then return CFG[r.id] end
        return r.def
    end
    local k = r.kind
    if k == "check" then return v == true end
    if k == "slider" then
        v = tonumber(v)
        if not v then return r.def end
        return clamp(floor(v + 0.5), r.lo, r.hi)
    end
    if k == "combo" then
        return combo_index(el, r.items) or r.def
    end
    if k == "color" then
        if type(v) == "table" and type(v.r) == "number" and type(v.g) == "number" and type(v.b) == "number" then return v end
        return r.def
    end
    if k == "multi" then
        if type(v) == "table" then return v end
        return r.def
    end
    return v
end

local function differs(kind, a, b)
    if kind == "color" and type(a) == "table" and type(b) == "table" then
        return a.r ~= b.r or a.g ~= b.g or a.b ~= b.b or a.a ~= b.a
    end
    if kind == "multi" then return not same(a, b) end
    return a ~= b
end

local function validate(r, v)
    local k = r.kind
    if k == "check" then
        if type(v) == "boolean" then return v end
    elseif k == "slider" then
        if type(v) == "number" then return clamp(floor(v + 0.5), r.lo, r.hi) end
    elseif k == "combo" then
        if type(v) == "number" then return clamp(floor(v + 0.5), 1, #r.items) end
    elseif k == "color" then
        if type(v) == "table" and type(v.r) == "number" and type(v.g) == "number" and type(v.b) == "number" then
            return { r = v.r, g = v.g, b = v.b, a = tonumber(v.a) or 255 }
        end
    elseif k == "multi" then
        if type(v) == "table" then return v end
    end
    return nil
end

local function write_el(r, v)
    local el = r.el
    if el.dummy then CFG[r.id] = v return end
    local k = r.kind
    if k == "combo" then
        set_combo(el, r.items, v)
    elseif k == "color" then
        pcall(el.set, el, color(v.r, v.g, v.b, v.a or 255))
    else
        pcall(el.set, el, v)
    end
end

local function derive()
    CFG.miss_win_s = (CFG.miss_win or 350) / 1000
    CFG.move_sc_f  = (CFG.move_sc or 35) / 100
    CFG.jit_sc_f   = (CFG.jit_sc or 50) / 100
end

local function preset_matches(idx)
    local p = PRESETS[idx]
    if not p then return true end
    for id, v in pairs(p) do
        if id ~= "name" and CFG[id] ~= v then return false end
    end
    return true
end

local cfg_tick -- forward

local function apply_preset(idx)
    local p = PRESETS[idx]
    if not p then return end
    PS.applying = true
    for id, v in pairs(p) do
        if id ~= "name" and REG[id] then write_el(REG[id], v) end
    end
    PS.applying = false
    cfg_tick(true)
    if CFG.notif then pcall(client.notify, "Preset \"" .. p.name .. "\" applied", META.name) end
end

-- force = values came from load / reset / the preset itself: the preset is not re-applied on top.
local function on_settings_changed(force)
    SET.dirty, SET.dirty_t = true, STATE.rt
    RB.eval_at = 0
    VIS.dirty = true
    if not REG.preset then return end
    local p = CFG.preset
    if p ~= PS.last then
        PS.last = p
        if p > 1 and not force and not PS.applying then
            apply_preset(p)
            return
        end
    end
    -- Values drifted away from the selected preset: show "Custom". If the widget refuses the
    -- programmatic change we stop arguing with the user.
    if p > 1 and PS.sync and not preset_matches(p) then
        write_el(REG.preset, 1)
        local back = read(REG.preset)
        CFG.preset, PS.last = back, back
        if back ~= 1 then PS.sync = false end
    end
end

cfg_tick = function(force)
    local rt = STATE.rt
    if not force and rt - MENU.last < (STATE.menu_open and 0.05 or 0.4) then return end
    MENU.last = rt
    local changed = false
    for i = 1, #ORDER do
        local id = ORDER[i]
        local r = REG[id]
        if r.kind ~= "key" then
            local v = read(r)
            if differs(r.kind, CFG[id], v) then
                CFG[id] = v
                changed = true
            end
        end
    end
    derive()
    if changed or force then on_settings_changed(force) end
end

-- ---------------------------------------------------------------- persistence
local LEGACY_MAP = { enable = "rb_enable", debug = "log_cfg", ind_on = "panel", ind_x = "panel_x",
                     ind_y = "panel_y", ind_scale = "panel_scale", ind_color = "accent" }

local function pack_settings()
    local t = {}
    for i = 1, #ORDER do
        local r = REG[ORDER[i]]
        local k, v = r.kind, CFG[r.id]
        if k == "check" or k == "slider" or k == "combo" then
            t[r.id] = v
        elseif k == "color" and type(v) == "table" then
            t[r.id] = { r = v.r, g = v.g, b = v.b, a = v.a }
        elseif k == "multi" and type(v) == "table" then
            local m = {}
            for j = 1, #r.items do m[r.items[j]] = multi_on(v, j, r.items) end
            t[r.id] = m
        end
    end
    return { v = 3, ver = META.version, persist = CFG.persist_ui ~= false, s = t }
end

local function settings_save()
    local ok, res = pcall(db.save, META.db_settings, pack_settings())
    return ok and res ~= false
end

local function settings_load()
    local ok, data = pcall(db.load, META.db_settings, nil)
    local legacy = false
    if not ok or type(data) ~= "table" or type(data.s) ~= "table" then
        ok, data = pcall(db.load, META.db_legacy, nil)
        if not ok or type(data) ~= "table" or type(data.s) ~= "table" then return false end
        legacy = true
    end
    if data.persist == false then return false end
    local n = 0
    for id, v in pairs(data.s) do
        local tid = legacy and (LEGACY_MAP[id] or id) or id
        local r = REG[tid]
        if r and r.kind ~= "key" then
            local val = validate(r, v)
            if val ~= nil then
                write_el(r, val)
                n = n + 1
            end
        end
    end
    if legacy and n > 0 then say("imported " .. n .. " settings from the s1 snapshot") end
    return n > 0
end

function ACT.reset_ui()
    PS.applying = true
    for i = 1, #ORDER do
        local r = REG[ORDER[i]]
        if r.kind ~= "key" then write_el(r, r.def) end
    end
    PS.applying = false
    PS.last = nil
    cfg_tick(true)
    if CFG.notif then pcall(client.notify, "Settings reset to defaults", META.name) end
end

-- ============================================================================
--  RESOLVER
-- ============================================================================
local function notify(msg)
    if CFG.notif ~= false then pcall(client.notify, msg, META.name) end
    say(msg)
end

RES.records, RES.by_pawn, RES.pending, RES.store = {}, {}, {}, {}
RES.insecure, RES.simtime_ok = false, true
RES.body_ok, RES.body_good, RES.body_bad = true, 0, 0
RES.last_purge, RES.total_hits, RES.total_misses, RES.total_shots = 0, 0, 0, 0
RES.write_cls, RES.write_ok, RES.write_fails = nil, nil, 0   -- write_ok: nil unknown, true working, false disabled
RES.focus = nil                                               -- record closest to the crosshair

-- ---------------------------------------------------------------- records
function RES.player_key(ctrl, pawn)
    if ctrl then
        local sid = safe(ctrl.steam_id, ctrl)
        if type(sid) == "string" and sid ~= "" and sid ~= "0" then return sid, true end
    end
    return "p" .. tostring(pawn:address()), false
end

function RES.new_record(key, is_sid)
    local rec = {
        key = key, is_sid = is_sid, name = "?",
        -- history ring buffers
        yaws = {}, pitches = {}, deltas = {}, head = 0, n = 0, dhead = 0, dn = 0,
        pitch_jit = 0, p_avg = 0, pitch_kind = "",
        -- classification
        mode = "static", mode_conf = 0, center = 0, amp = 0, spin_rate = 0, mean_abs = 0, jit_alt = 0,
        -- hints
        body_delta = 0, fs_hint = 0, mv_hint = 0, md_hint = 0, score = 0,
        last_move_yaw = nil, last_move_t = 0, moving = false, speed = 0,
        -- learning
        side = 1, conf = 0.3, pred_side = 1, brute_idx = 1,
        shots = 0, hits = 0, misses = 0, kills = 0, hit_streak = 0, miss_streak = 0,
        last_hit_t = 0, last_miss_t = 0, last_shot_t = -1e9, reveal_t = -1e9,
        prev_result = nil, hit_side = 0, ab_score = 0, ab_flips = 0, preflipped = false,
        -- output
        at_target = 0, raw_yaw = 0, raw_pitch = 0, amount = 0,
        resolved_yaw = 0, resolved_pitch = 0, resolved = false, applied = false,
        -- bookkeeping
        sim_time = nil, last_tick = -1, seen_rt = 0, pawn = nil, pawn_addr = nil, en_eye = nil,
    }
    local saved = (is_sid and CFG.persist) and RES.store[key] or nil
    if type(saved) == "table" then
        rec.side   = (saved.side == -1) and -1 or 1
        rec.conf   = clamp((tonumber(saved.conf) or 0) * 0.6, 0, 0.6)
        rec.hits   = tonumber(saved.hits) or 0
        rec.misses = tonumber(saved.misses) or 0
    end
    return rec
end

function RES.get_record(ctrl, pawn)
    local key, is_sid = RES.player_key(ctrl, pawn)
    local rec = RES.records[key]
    if not rec then
        rec = RES.new_record(key, is_sid)
        rec.name = (ctrl and safe(ctrl.name, ctrl)) or safe(pawn.name, pawn) or "?"
        RES.records[key] = rec
    end
    local addr = pawn:address()
    if rec.pawn_addr ~= addr then
        if rec.pawn_addr and RES.by_pawn[rec.pawn_addr] == rec then RES.by_pawn[rec.pawn_addr] = nil end
        rec.pawn_addr = addr
        RES.by_pawn[addr] = rec
    end
    rec.pawn = pawn
    return rec
end

function RES.record_by_pawn(pawn)
    if not pawn then return nil end
    local addr = safe(pawn.address, pawn)
    return addr and RES.by_pawn[addr] or nil
end

function RES.remember(rec)
    if not rec.is_sid then return end
    RES.store[rec.key] = { side = rec.side, conf = rec.conf, hits = rec.hits, misses = rec.misses, t = os.time() }
end

function RES.store_load()
    local data = safe(db.load, META.db, {})
    RES.store = (type(data) == "table") and data or {}
end

function RES.store_save()
    if not CFG.persist then return end
    local list = {}
    for k, v in pairs(RES.store) do
        if type(v) == "table" then list[#list + 1] = { k = k, t = tonumber(v.t) or 0 } end
    end
    if #list > C.DB_MAX then
        tsort(list, function(a, b) return a.t > b.t end)
        for i = C.DB_MAX + 1, #list do RES.store[list[i].k] = nil end
    end
    safe(db.save, META.db, RES.store)
end

-- ---------------------------------------------------------------- history + classification
function RES.push_history(rec, yaw, pitch)
    local H = C.HISTORY
    if rec.n > 0 then
        local prev_yaw, prev_pitch = rec.yaws[rec.head], rec.pitches[rec.head]
        rec.dhead = rec.dhead % H + 1
        rec.deltas[rec.dhead] = normalize(yaw - prev_yaw)
        rec.dn = min(H, rec.dn + 1)
        if abs(pitch - prev_pitch) > 45 then
            rec.pitch_jit = min(6, rec.pitch_jit + 1)
        else
            rec.pitch_jit = max(0, rec.pitch_jit - 0.5)
        end
        rec.p_avg = lerp(rec.p_avg, pitch, 0.3)
    else
        rec.p_avg = pitch
    end
    rec.head = rec.head % H + 1
    rec.yaws[rec.head] = yaw
    rec.pitches[rec.head] = pitch
    rec.n = min(H, rec.n + 1)
end

function RES.circular_mean(rec)
    local sx, sy = 0, 0
    for i = 1, rec.n do
        local a = rad(rec.yaws[i])
        sx, sy = sx + cos(a), sy + sin(a)
    end
    if sx == 0 and sy == 0 then return rec.yaws[rec.head] end
    return normalize(deg(atan2(sy, sx)))
end

-- static / sway / jitter / spin / random from the delta window, plus a pitch class.
function RES.classify(rec)
    local dn = rec.dn
    if dn < 3 then
        rec.mode, rec.mode_conf = "static", 0
        return
    end
    local H = C.HISTORY
    local sum_abs, sum_signed, flips, big, prev_sign, alt, pairs_n = 0, 0, 0, 0, 0, 0, 0
    local prev_d
    local idx = (dn == H) and (rec.dhead % H + 1) or 1
    for _ = 1, dn do
        local d = rec.deltas[idx]
        local ad = abs(d)
        sum_abs, sum_signed = sum_abs + ad, sum_signed + d
        if ad > C.JITTER_MIN_DELTA then
            big = big + 1
            local s = (d > 0) and 1 or -1
            if prev_sign ~= 0 and s ~= prev_sign then flips = flips + 1 end
            prev_sign = s
        end
        if prev_d then
            pairs_n = pairs_n + 1
            local m = max(ad, abs(prev_d))
            -- two consecutive deltas of equal size and opposite sign = two-way jitter
            if m > C.JITTER_MIN_DELTA * 0.5 and abs(d + prev_d) < max(4, 0.35 * m) then alt = alt + 1 end
        end
        prev_d = d
        idx = idx % H + 1
    end

    local mean_abs, mean_signed = sum_abs / dn, sum_signed / dn
    rec.mean_abs = mean_abs
    rec.jit_alt = (pairs_n > 0) and (alt / pairs_n) or 0

    if abs(mean_signed) > C.SPIN_MIN_RATE and big >= dn * 0.6 and flips <= 1 then
        rec.mode, rec.spin_rate, rec.mode_conf = "spin", mean_signed, min(1, big / dn)
    elseif big >= dn * 0.4 and flips >= max(2, floor(big * 0.5)) then
        rec.mode = "jitter"
        rec.center = RES.circular_mean(rec)
        local amp = 0
        for i = 1, rec.n do amp = amp + abs(normalize(rec.yaws[i] - rec.center)) end
        rec.amp = amp / rec.n
        rec.mode_conf = min(1, (flips / max(1, big - 1)) * 0.5 + rec.jit_alt * 0.5)
    elseif mean_abs < C.STATIC_MAX_DELTA then
        rec.mode, rec.mode_conf = "static", 1 - mean_abs / C.STATIC_MAX_DELTA
    elseif mean_abs < C.SWAY_MAX_DELTA then
        rec.mode, rec.center, rec.mode_conf = "sway", RES.circular_mean(rec), 0.7
    else
        rec.mode, rec.center, rec.mode_conf = "random", RES.circular_mean(rec), 0.5
    end

    if rec.pitch_jit >= 3 then rec.pitch_kind = "FLICK"
    elseif rec.p_avg >= 80 then rec.pitch_kind = "DOWN"
    elseif rec.p_avg <= -80 then rec.pitch_kind = "UP"
    elseif abs(rec.p_avg) < 3 and rec.mode ~= "static" then rec.pitch_kind = "ZERO"
    else rec.pitch_kind = "" end
end

-- ---------------------------------------------------------------- hints
local function hb_kind(h)
    local g = h.group
    if g == 4 then return "la" elseif g == 5 then return "ra"
    elseif g == 6 then return "ll" elseif g == 7 then return "rl" end
    local n = h.group_name
    if type(n) == "string" then
        n = s_lower(n)
        local left = s_find(n, "left", 1, true) ~= nil
        local right = s_find(n, "right", 1, true) ~= nil
        if s_find(n, "arm", 1, true) then
            if left then return "la" elseif right then return "ra" end
        elseif s_find(n, "leg", 1, true) then
            if left then return "ll" elseif right then return "rl" end
        end
    end
    return nil
end

-- Body yaw from a left/right hitbox pair (highest hitbox of each group).
local function pair_yaw(hbs, lk, rk)
    local L, R
    for i = 1, #hbs do
        local h = hbs[i]
        local c = h.center
        if c then
            local k = hb_kind(h)
            if k == lk then
                if not L or c.z > L.z then L = c end
            elseif k == rk then
                if not R or c.z > R.z then R = c end
            end
        end
    end
    if not L or not R then return nil end
    local dx, dy = L.x - R.x, L.y - R.y
    if dx * dx + dy * dy < 4 then return nil end
    return normalize(deg(atan2(dy, dx)) - 90)   -- (L - R) is the body's left vector
end

function RES.body_hint(rec, pawn, yaw)
    if not RES.body_ok then return 0 end
    local hbs = safe(pawn.hitboxes, pawn)
    if type(hbs) ~= "table" then
        RES.body_bad = RES.body_bad + 1
        if RES.body_bad > 40 then RES.body_ok = false end
        return 0
    end
    local ref = pair_yaw(hbs, "ll", "rl") or pair_yaw(hbs, "la", "ra")
    if not ref then return 0 end
    local d = normalize(ref - yaw)
    if abs(d) > C.BODY_SANE_DELTA then
        RES.body_bad = RES.body_bad + 1
        if RES.body_bad > 40 and RES.body_good < RES.body_bad / 8 then
            RES.body_ok = false
            notify("Body yaw hint disabled (hitbox data not usable)")
        end
        return 0
    end
    RES.body_good = RES.body_good + 1
    rec.body_delta = d
    if abs(d) < C.BODY_MIN_DELTA then return 0 end
    return clamp(d / C.BODY_MAX_DELTA, -1, 1)
end

-- Which side of the enemy head is covered from our point of view.
-- Side +1 (CCW) moves the head toward OUR right, so right cover => +1.
function RES.freestand_hint(lp, pawn, lp_eye, en_eye)
    local yaw = rad((en_eye - lp_eye):angles().y)
    local right = vector(sin(yaw), -cos(yaw), 0)
    local opts = { skip = { lp, pawn }, mask = MASK_VISIBLE }
    local tl = safe(trace.line, lp_eye, en_eye - right * C.FS_OFFSET, opts)
    local tr = safe(trace.line, lp_eye, en_eye + right * C.FS_OFFSET, opts)
    if type(tl) ~= "table" or type(tr) ~= "table" then return 0 end
    local fl, fr = tonumber(tl.fraction) or 1, tonumber(tr.fraction) or 1
    local bl, br = fl < 0.98, fr < 0.98
    if bl == br then return 0 end
    return br and 1 or -1
end

function RES.movement_hint(rec, yaw, now)
    if rec.moving or not rec.last_move_yaw then return 0 end
    local age = now - rec.last_move_t
    if age < 0 or age > C.MOVE_MEM_TIME then return 0 end
    local d = normalize(rec.last_move_yaw - yaw)
    if abs(d) < 20 then return 0 end
    return sign(d) * (1 - age / C.MOVE_MEM_TIME)
end

-- ---------------------------------------------------------------- decision
function RES.brute_len()
    return (CFG.brute_pat == PAT_STEP) and STEP_N or BRUTE_N
end

-- multiplier and absolute amount for the current brute index / mode
function RES.brute_entry(rec)
    local m = CFG.mode
    if m == MODE_STATIC or m == MODE_OFFSET then return 1, CFG.desync end
    if CFG.brute_pat == PAT_STEP then
        local i = (rec.brute_idx - 1) % STEP_N + 1
        return STEP_SEQ[i], STEP_SEQ[i] * CFG.brute_step
    end
    local i = (rec.brute_idx - 1) % BRUTE_N + 1
    return BRUTE[i], BRUTE[i] * CFG.desync
end

function RES.decide_side(rec, b, fs, mv, md)
    rec.fs_hint, rec.mv_hint, rec.md_hint = fs, mv, md
    if CFG.mode == MODE_BRUTE or CFG.mode == MODE_OFFSET then
        rec.score, rec.pred_side = rec.side, rec.side
        return
    end
    local score = rec.side * rec.conf * C.W_LEARNED
    if CFG.body then score = score + b * C.W_BODY end
    if CFG.freestand then score = score + fs * C.W_FREESTAND end
    if CFG.move_mem then score = score + mv * C.W_MOVE end
    if CFG.move_dir then score = score + md * C.W_MOVEDIR end
    rec.score = score
    if abs(score) >= C.SIDE_DEADZONE then
        rec.pred_side = (score > 0) and 1 or -1
    end
end

function RES.resolve_pitch(rec, pitch)
    local pm = CFG.pitch
    if pm == PITCH_OFF then return pitch end
    if pm == PITCH_CLAMP then return clamp(pitch, -89, 89) end
    if pm == PITCH_DOWN then return 89 end
    if pm == PITCH_ZERO then return 0 end
    if pm == PITCH_UP then return -89 end
    if pitch > 89.5 then return 89 end
    if pitch < -89.5 then return -89 end
    if rec.pitch_jit >= 3 then return 89 end          -- fake-pitch flicker: assume looking down
    return clamp(pitch, -89, 89)
end

function RES.compute(rec, yaw, pitch)
    local mode, m = rec.mode, CFG.mode
    local at = rec.at_target

    if m == MODE_OFFSET then
        rec.amount = CFG.yaw_off
        rec.resolved_yaw = normalize(at + CFG.yaw_off)
        rec.resolved_pitch = RES.resolve_pitch(rec, pitch)
        rec.resolved = true
        return
    end

    local base
    if CFG.base == BASE_TARGET then
        base = at
    elseif CFG.base == BASE_EYE then
        base = yaw
    elseif mode == "spin" then
        base = at
    elseif mode == "jitter" or mode == "sway" then
        base = rec.center
    elseif mode == "random" and rec.mean_abs > C.RANDOM_CENTER_AT then
        base = rec.center
    else
        base = yaw
    end
    if m == MODE_JITSPIN then
        if mode == "spin" then
            base = normalize(yaw + rec.spin_rate * C.SPIN_LEAD)
        elseif mode == "jitter" then
            base = rec.center
        end
    end

    local _, amount = RES.brute_entry(rec)
    if mode == "jitter" then
        amount = amount * CFG.jit_sc_f
    elseif mode == "random" then
        amount = amount * 0.75
    elseif mode == "spin" and m == MODE_JITSPIN then
        amount = amount * 0.5
    end
    if rec.moving then amount = amount * CFG.move_sc_f end
    if CFG.face_damp and (mode == "static" or mode == "sway") and abs(normalize(yaw - at)) < C.FACE_ANGLE then
        amount = amount * C.FACE_SCALE
    end

    rec.amount = amount
    rec.resolved_yaw = normalize(base + rec.pred_side * amount)
    rec.resolved_pitch = RES.resolve_pitch(rec, pitch)
    rec.resolved = true
end

-- Little trust in the current guess: the ragebot assist prefers the body and adjusts hitchance.
function RES.unresolved(rec)
    if not rec or not rec.resolved then return false end
    if rec.miss_streak >= 2 or rec.brute_idx >= 3 then return true end
    if rec.mode == "random" then return rec.conf < 0.5 end
    if rec.mode == "jitter" and rec.amp > 35 then return rec.conf < 0.5 end
    return false
end

-- ---------------------------------------------------------------- memory write
function RES.apply(pawn, rec)
    rec.applied = false
    if not CFG.apply or not RES.insecure or RES.write_ok == false then return end
    local ang = vector(rec.resolved_pitch, rec.resolved_yaw, 0)

    if RES.write_cls then
        if pcall(pawn.set, pawn, RES.write_cls, "m_angEyeAngles", "vector", ang) then
            rec.applied = true
            RES.write_fails = 0
        else
            RES.write_fails = RES.write_fails + 1
            if RES.write_fails > 20 then
                RES.write_ok = false
                notify("Eye angle override failing; switched to tracking only")
            end
        end
        return
    end

    for i = 1, #EYE_CLASSES do
        if pcall(pawn.set, pawn, EYE_CLASSES[i], "m_angEyeAngles", "vector", ang) then
            RES.write_cls, RES.write_ok, rec.applied = EYE_CLASSES[i], true, true
            return
        end
    end
    RES.write_ok = false
    notify("m_angEyeAngles not found in schema; tracking only")
end

function RES.read_simtime(pawn)
    if not RES.simtime_ok then return nil end
    local ok, v = pcall(pawn.get, pawn, "C_BaseEntity", "m_flSimulationTime", "float")
    if ok and type(v) == "number" then return v end
    RES.simtime_ok = false
    return nil
end

-- ---------------------------------------------------------------- per-player update
function RES.process(pawn, ctrl, lp, lp_alive, lp_eye, now, tick, rt)
    local rec = RES.get_record(ctrl, pawn)
    rec.seen_rt = rt

    local eye = pawn:eye_angles()
    local yaw, pitch = normalize(eye.y), eye.x

    -- Freshness gate: only analyse genuinely new network data.
    local simt = RES.read_simtime(pawn)
    local fresh
    if simt then
        fresh = (simt ~= rec.sim_time)
        rec.sim_time = simt
    else
        fresh = (tick ~= rec.last_tick)
        -- Echo guard: without simulation time we could read back our own write.
        if fresh and rec.applied
            and abs(normalize(yaw - rec.resolved_yaw)) < 0.01
            and abs(pitch - rec.resolved_pitch) < 0.01 then
            fresh = false
        end
    end
    rec.last_tick = tick

    -- A sample right after the enemy fired carries his aim yaw, not his anti-aim.
    if not fresh or (now - rec.reveal_t) < C.REVEAL_TIME then
        if rec.resolved then RES.apply(pawn, rec) end
        return rec
    end

    local vel = pawn:velocity()
    local speed = vel:length2d()
    rec.raw_yaw, rec.raw_pitch, rec.speed = yaw, pitch, speed
    RES.push_history(rec, yaw, pitch)
    RES.classify(rec)

    if speed > C.MOVE_SPEED then
        rec.moving = true
        rec.last_move_yaw = normalize(vel:angles().y)
        rec.last_move_t = now
    else
        rec.moving = false
    end

    local en_eye = pawn:eye_position()
    rec.en_eye = en_eye
    rec.at_target = normalize(calc_angle(en_eye, lp_eye).y)

    local b  = CFG.body and RES.body_hint(rec, pawn, yaw) or 0
    local fs = (CFG.freestand and lp_alive) and RES.freestand_hint(lp, pawn, lp_eye, en_eye) or 0
    local mv = CFG.move_mem and RES.movement_hint(rec, yaw, now) or 0
    local md = 0
    if CFG.move_dir and speed > C.MOVEDIR_SPEED and rec.last_move_yaw then
        md = sign(normalize(rec.last_move_yaw - rec.at_target))
    end

    RES.decide_side(rec, b, fs, mv, md)
    RES.compute(rec, yaw, pitch)
    RES.apply(pawn, rec)
    return rec
end

-- ---------------------------------------------------------------- shot feedback
function RES.on_hit(rec, hitgroup, dmg)
    local pending, shot = RES.pending, nil
    for i = #pending, 1, -1 do
        if pending[i].key == rec.key then
            shot = shot or pending[i]
            tremove(pending, i)
        end
    end
    rec.hits, rec.hit_streak, rec.miss_streak = rec.hits + 1, rec.hit_streak + 1, 0
    rec.last_hit_t = globals.curtime()
    RES.total_hits = RES.total_hits + 1

    local head = (hitgroup == 1)
    local partial = CFG.body_partial and not head and not (shot and shot.baim)
    local used_side = shot and shot.side or rec.pred_side
    local m = RES.brute_entry(rec)
    if not partial and m ~= 0 then
        rec.side = sign(used_side * m)
        if CFG.brute_pat ~= PAT_STEP and abs(m) == 1 then rec.brute_idx = 1 end
    end

    -- anti-anti-bruteforce: a second hit in a row that only landed on the other side means he
    -- flips after every hit; a second hit on the same side means he does not.
    if rec.prev_result == "hit" then
        if rec.preflipped or used_side ~= rec.hit_side then
            rec.ab_score = min(3, rec.ab_score + 1)
        else
            rec.ab_score = max(0, rec.ab_score - 1)
        end
    end
    rec.hit_side, rec.prev_result, rec.preflipped = used_side, "hit", false
    rec.conf = min(1, rec.conf + C.HIT_CONF_GAIN * (head and 1.25 or (partial and C.PARTIAL_GAIN or 1)))

    local pre = ""
    if CFG.anti_ab and rec.ab_score >= 2 and not partial then
        rec.side = -rec.side                      -- he will flip after this hit: be there first
        rec.ab_flips = rec.ab_flips + 1
        rec.preflipped = true
        pre = "  · pre-flip"
    end
    RES.remember(rec)
    VIS.push(head and "hit" or "body", format("%s  %s %d%s%s", rec.name, head and "HEAD" or "BODY",
        floor(tonumber(dmg) or 0), partial and " (partial)" or "", pre))
end

function RES.on_miss(shot, rec)
    rec.misses, rec.hit_streak = rec.misses + 1, 0
    rec.last_miss_t = globals.curtime()
    RES.total_misses = RES.total_misses + 1
    rec.conf = max(0, rec.conf - C.MISS_CONF_LOSS)
    local prev = rec.prev_result
    rec.prev_result = "miss"

    if shot.moving or shot.lp_air then
        -- moving targets / airborne shooter miss for many reasons; do not step the brute table
        RES.remember(rec)
        VIS.push("miss", format("%s  MISS (%s)", rec.name, shot.moving and "moving" or "airborne"))
        return
    end
    if prev == "hit" and CFG.anti_ab then
        if rec.preflipped then
            rec.ab_score = max(0, rec.ab_score - 1)   -- the pre-flip was wrong
            rec.preflipped = false
        elseif shot.side == rec.hit_side then
            rec.ab_score = min(3, rec.ab_score + 1)   -- same side missed right after a hit: he flipped
        end
    end
    rec.miss_streak = rec.miss_streak + 1
    local info = ""
    if rec.miss_streak >= CFG.miss_tol then
        rec.miss_streak = 0
        if CFG.mode == MODE_STATIC or CFG.mode == MODE_OFFSET then
            rec.side = -rec.side
            info = "  -> flip"
        else
            rec.brute_idx = rec.brute_idx % RES.brute_len() + 1
            info = format("  -> brute %d", rec.brute_idx)
        end
    end
    RES.remember(rec)
    VIS.push("miss", format("%s  MISS%s", rec.name, info))
end

function RES.check_pending(now)
    local pending = RES.pending
    for i = #pending, 1, -1 do
        local s = pending[i]
        if now - s.t > CFG.miss_win_s then
            tremove(pending, i)
            local rec = RES.records[s.key]
            if rec then RES.on_miss(s, rec) end
        elseif now < s.t then
            tremove(pending, i)   -- clock went backwards (map change)
        end
    end
end

function RES.find_shot_target(lp)
    local from = lp:eye_position()
    local angs = { safe(engine.view_angles), STATE.cmd_angles }
    for i = 1, 2 do
        local a = angs[i]
        if a then
            local r = safe(trace.bullet, from, from + a:forward() * 8192)
            if type(r) == "table" and r.hit and r.entity then
                local rec = RES.record_by_pawn(r.entity)
                if rec then return rec end
            end
        end
    end
    -- ragebot assist target (closest to the crosshair, already filtered)
    if RB.t_addr then
        local rec = RES.by_pawn[RB.t_addr]
        if rec then return rec end
    end
    -- fallback: closest tracked enemy within 12 degrees
    local va = angs[1]
    if not va then return nil end
    local best, best_fov = nil, 12
    local rt = globals.realtime()
    for _, rec in pairs(RES.records) do
        if rec.pawn and rt - rec.seen_rt < 0.2 then
            local ep = safe(rec.pawn.eye_position, rec.pawn)
            if ep then
                local want = calc_angle(from, ep)
                local dy = abs(normalize(want.y - va.y))
                local dp = abs(want.x - va.x)
                local fov = sqrt(dy * dy + dp * dp)
                if fov < best_fov then best, best_fov = rec, fov end
            end
        end
    end
    return best
end

function RES.is_local_controller(ctrl)
    if not ctrl then return false end
    local lc = entity.local_controller()
    if not lc then return false end
    return ctrl:address() == lc:address()
end

function RES.on_weapon_fire(ev)
    if not CFG.enable then return end
    local ctrl = safe(ev.get_controller, ev, "userid")
    if not ctrl then return end
    if not RES.is_local_controller(ctrl) then
        local rec = RES.record_by_pawn(safe(ev.get_pawn, ev, "userid")) or RES.record_by_pawn(safe(ctrl.pawn, ctrl))
        if rec then rec.reveal_t = globals.curtime() end
        return
    end
    if not CFG.feedback then return end
    local lp = entity.local_pawn()
    if not lp then return end
    local info = safe(lp.weapon_info, lp)
    if type(info) == "table" and info.gun == false then return end

    local rec = RES.find_shot_target(lp)
    if not rec then return end
    local now = globals.curtime()
    rec.shots = rec.shots + 1
    RES.total_shots = RES.total_shots + 1
    if now - rec.last_shot_t < C.SHOT_DEDUPE then return end   -- spray: one pending shot per slice
    rec.last_shot_t = now
    local pending = RES.pending
    pending[#pending + 1] = {
        key = rec.key, t = now, side = rec.pred_side, idx = rec.brute_idx, mode = rec.mode,
        moving = rec.moving, lp_air = STATE.lp_air, baim = RB.baim ~= nil,
    }
    if #pending > C.PENDING_MAX then tremove(pending, 1) end
end

function RES.on_player_hurt(ev)
    if not CFG.enable or not CFG.feedback then return end
    local att = safe(ev.get_controller, ev, "attacker")
    local vic = safe(ev.get_controller, ev, "userid")
    local lc = entity.local_controller()
    if not lc then return end
    local la = lc:address()

    if att and att:address() == la then
        local rec = RES.record_by_pawn(safe(ev.get_pawn, ev, "userid"))
        if not rec and vic then
            local sid = safe(vic.steam_id, vic)
            if sid then rec = RES.records[sid] end
            if not rec then rec = RES.record_by_pawn(safe(vic.pawn, vic)) end
        end
        if not rec then return end
        RES.on_hit(rec, safe(ev.get_int, ev, "hitgroup") or 0, safe(ev.get_int, ev, "dmg_health") or 0)
    elseif CFG.flip_on_hurt and att and vic and vic:address() == la then
        local rec = RES.record_by_pawn(safe(ev.get_pawn, ev, "attacker")) or RES.record_by_pawn(safe(att.pawn, att))
        if rec then
            rec.side = -rec.side
            RES.remember(rec)
        end
    end
end

function RES.reset_history(rec)
    rec.n, rec.dn, rec.head, rec.dhead = 0, 0, 0, 0
    rec.pitch_jit, rec.pitch_kind = 0, ""
    rec.mode, rec.mode_conf = "static", 0
    rec.resolved, rec.applied = false, false
    rec.sim_time, rec.last_move_yaw = nil, nil
    rec.miss_streak = 0
end

function RES.on_player_death(ev)
    if not CFG.enable then return end
    local rec = RES.record_by_pawn(safe(ev.get_pawn, ev, "userid"))
    if not rec then
        local vic = safe(ev.get_controller, ev, "userid")
        if vic then
            local sid = safe(vic.steam_id, vic)
            if sid then rec = RES.records[sid] end
        end
    end
    if not rec then return end
    local pending = RES.pending
    for i = #pending, 1, -1 do
        if pending[i].key == rec.key then tremove(pending, i) end
    end
    RES.reset_history(rec)
    local att = safe(ev.get_controller, ev, "attacker")
    if att and RES.is_local_controller(att) then
        rec.kills = rec.kills + 1
        VIS.push("kill", format("%s  KILL  (%d/%d)", rec.name, rec.hits, rec.misses))
    end
end

-- ---------------------------------------------------------------- frame stage
function RES.reapply_all()
    local players = safe(entity.players)
    if type(players) ~= "table" then return end
    for i = 1, #players do
        local pawn = players[i].pawn
        if pawn then
            local rec = RES.by_pawn[pawn:address()]
            if rec and rec.resolved and safe(pawn.alive, pawn) then RES.apply(pawn, rec) end
        end
    end
end

function RES.purge(rt)
    if rt - RES.last_purge < 5 then return end
    RES.last_purge = rt
    for key, rec in pairs(RES.records) do
        if rt - rec.seen_rt > C.PURGE_AFTER then
            if rec.pawn_addr and RES.by_pawn[rec.pawn_addr] == rec then RES.by_pawn[rec.pawn_addr] = nil end
            RES.records[key] = nil
        end
    end
end

function RES.frame(st)
    if st ~= STAGE_NET_END and st ~= STAGE_LAGCOMP then return end
    STATE.rt = globals.realtime()
    cfg_tick(false)
    if not CFG.enable or not engine.in_game() then
        RES.focus = nil
        return
    end
    RES.insecure = safe(client.insecure) == true
    STATE.insecure = RES.insecure

    if st == STAGE_LAGCOMP then
        RES.reapply_all()
        return
    end

    local lp = entity.local_pawn()
    if not lp then return end
    local lp_alive = safe(lp.alive, lp) == true
    local lp_eye = safe(lp.eye_position, lp)
    if not lp_eye then return end

    local now, tick, rt = globals.curtime(), globals.tickcount(), STATE.rt
    local va = safe(engine.view_angles)
    local players = entity.players()
    local focus, focus_fov = nil, C.FOCUS_FOV
    for i = 1, #players do
        local p = players[i]
        local pawn = p.pawn
        if pawn and pawn:alive() and pawn:is_enemy() then
            local ok, rec = pcall(RES.process, pawn, p.controller, lp, lp_alive, lp_eye, now, tick, rt)
            if not ok then
                if CFG.debug then say("process error: " .. tostring(rec)) end
            elseif rec and va and rec.en_eye then
                local want = calc_angle(lp_eye, rec.en_eye)
                local dy = abs(normalize(want.y - va.y))
                local dp = abs(want.x - va.x)
                local fov = sqrt(dy * dy + dp * dp)
                if fov < focus_fov then focus, focus_fov = rec, fov end
            end
        end
    end
    RES.focus = focus

    if CFG.feedback then RES.check_pending(now) end
    RES.purge(rt)
end

-- ---------------------------------------------------------------- lifecycle
function RES.reset_volatile()
    RES.pending = {}
    for _, rec in pairs(RES.records) do
        RES.reset_history(rec)
        rec.conf = rec.conf * C.ROUND_CONF_DECAY
    end
end

function ACT.reset_learn()
    RES.records, RES.by_pawn, RES.pending, RES.store = {}, {}, {}, {}
    RES.total_hits, RES.total_misses, RES.total_shots = 0, 0, 0
    RES.focus = nil
    safe(db.save, META.db, {})
    notify("Learned data cleared")
end

function RES.on_round_start()
    RES.reset_volatile()
    RES.store_save()
end

function RES.on_level_init()
    RES.records, RES.by_pawn, RES.pending = {}, {}, {}
    RES.focus = nil
    RES.body_good, RES.body_bad, RES.body_ok = 0, 0, true
    RES.simtime_ok = true
    RES.write_fails = 0
    if RES.write_ok == false then RES.write_ok, RES.write_cls = nil, nil end
end

function RES.on_level_shutdown()
    RES.store_save()
    RES.records, RES.by_pawn, RES.pending = {}, {}, {}
    RES.focus = nil
end

-- ============================================================================
--  RAGEBOT ASSIST (ported from s1 v3.2)
--  There is no ragebot module in the API, so values are read and written through
--  config.get / config.set. Paths are discovered from config.keys; originals are
--  journaled in db and returned when the assist stands down.
-- ============================================================================
RB.tick_n, RB.cm_t, RB.paint_t, RB.hk_t = 0, -1e9, -1e9, -1e9
RB.air_ticks, RB.land_soon, RB.sim_fail, RB.g_tick, RB.sync_mode = 0, false, 0, K.GRAVITY * 0.015625, false
RB.state, RB.wgroup, RB.waddr, RB.wtick, RB.eval_at = nil, nil, nil, -1e9, 0
RB.t_hp, RB.t_air, RB.t_move, RB.t_addr, RB.t_unres, RB.t_name = nil, false, false, nil, false, nil
RB.baim_reason, RB.baim_until, RB.base_hc, RB.base_dmg = nil, 0, nil, nil
RB.hc, RB.dmg, RB.safe, RB.baim, RB.strict, RB.pub_thp = nil, nil, false, nil, false, nil
RB.touched, RB.paused, RB.in_game = false, false, true
RB.boot_status = "—"

local function is_head_name(x)
    if type(x) ~= "string" then return false end
    local l = s_lower(x)
    return s_find(l, "head", 1, true) ~= nil and s_find(l, "ahead", 1, true) == nil
end

-- Removes the head entry from a hitbox multi-select value. Returns the new value, the
-- original (head was not enabled) or nil (unsupported format or head is the only hitbox).
local function strip_head(v)
    if type(v) ~= "table" then return nil end
    local out, enabled, changed = {}, 0, false
    if #v > 0 then
        for i = 1, #v do
            local x = v[i]
            if type(x) ~= "string" then return nil end
            if is_head_name(x) then
                changed = true
            else
                out[#out + 1] = x
                enabled = enabled + 1
            end
        end
    else
        for k, x in pairs(v) do
            if type(k) ~= "string" then return nil end
            if is_head_name(k) and x then
                out[k] = false
                changed = true
            else
                out[k] = x
                if x then enabled = enabled + 1 end
            end
        end
    end
    if not changed then return v end
    if enabled == 0 then return nil end
    return out
end

local function fmt_v(v)
    local tv = type(v)
    if tv == "number" then
        if v == floor(v) then return format("%d", v) end
        return format("%.2f", v)
    elseif tv == "table" then
        local parts, n = {}, 0
        for k, x in pairs(v) do
            n = n + 1
            if n > 8 then parts[#parts + 1] = ".." break end
            parts[#parts + 1] = (type(k) == "number") and tostring(x) or (tostring(k) .. "=" .. tostring(x))
        end
        return "{" .. tconcat(parts, ",") .. "}"
    end
    return tostring(v)
end

local function cfg_get(path)
    local ok, v = pcall(config.get, path)
    if ok then return v end
    return nil
end

local function cfg_set(path, v)
    local ok, r = pcall(config.set, path, v)
    return ok and r ~= false
end

-- ---------------------------------------------------------------- journal
-- data: originals of paths currently overridden (or whose restore failed). disk: copy of the
-- file. The file is rewritten when an entry is missing (immediately) or stale (lazily).
Journal.data, Journal.disk = {}, {}
Journal.add_dirty, Journal.rm_dirty, Journal.rm_t = false, false, 0

function Journal.add(path, orig)
    local v = copy(orig)
    Journal.data[path] = v
    if not same(Journal.disk[path], v) then Journal.add_dirty = true end
end

function Journal.remove(path)
    if Journal.data[path] == nil then return end
    Journal.data[path] = nil
    if Journal.disk[path] ~= nil then Journal.rm_dirty, Journal.rm_t = true, STATE.rt end
end

local function journal_missing()
    for k, v in pairs(Journal.data) do
        if not same(Journal.disk[k], v) then return true end
    end
    return false
end

local function journal_stale()
    for k in pairs(Journal.disk) do
        if Journal.data[k] == nil then return true end
    end
    return false
end

function Journal.flush(force)
    local need = false
    if Journal.add_dirty then
        need = journal_missing()
        if not need then Journal.add_dirty = false end
    end
    if not need and Journal.rm_dirty and (force or STATE.rt - Journal.rm_t >= K.JOURNAL_LAZY) then
        need = journal_stale()
        if not need then Journal.rm_dirty = false end
    end
    if not need then return end
    if not force and STATE.rt - SET.io_t < K.IO_RETRY then return end
    local ok, res = pcall(db.save, META.db_journal, Journal.data)
    if ok and res ~= false then
        local disk = {}
        for k, v in pairs(Journal.data) do disk[k] = copy(v) end
        Journal.disk = disk
        Journal.add_dirty, Journal.rm_dirty = false, false
    else
        SET.io_t = STATE.rt
    end
end

-- Returns config values left in the journal by a crash. What cannot be restored stays in
-- the journal: the next capture of that path takes its original from there.
function Journal.restore()
    local ok, saved = pcall(db.load, META.db_journal, nil)
    if not ok or type(saved) ~= "table" then return 0 end
    local n, any = 0, false
    for path, val in pairs(saved) do
        if type(path) == "string" and val ~= nil and val ~= json.null then
            any = true
            Journal.disk[path] = copy(val)
            local cur = cfg_get(path)
            if cur ~= nil and type(cur) == type(val) and not same(cur, val) then
                if cfg_set(path, val) then
                    n = n + 1
                else
                    Journal.data[path] = copy(val)
                end
            end
        end
    end
    if any then Journal.rm_dirty, Journal.rm_t = true, -1e9 end
    return n
end

-- ---------------------------------------------------------------- config binding
local NONE = {}          -- "original not captured"
local TRANSFORM = {}     -- "value derived from the original" (flags, lists)

local GENERIC_EXCLUDE = {
    "colou?r", "visual", "%f[%w]esp%f[%W]", "chams", "glow", "indicator", "draw", "show",
    "%f[%w]logs?%f[%W]", "legit", "trigger", "%f[%w]keys?%f[%W]", "hotkey", "bind", "sound",
    "notif", "%f[%w]hud%f[%W]", "font", "preview", "widget", "overr", "%f[%w]ovr%f[%W]",
}

local ORDER_P = { "hc", "dmg", "safe", "baim", "hitbox" }
local SL = {
    hc = { tag = "HC", title = "Hitchance",
           patterns = { "hit[%s_%.%-]?chance" }, exclude = {},
           ok = function(v) return type(v) == "number" and v >= 0 and v <= 100 end },
    dmg = { tag = "DMG", title = "Min damage",
            patterns = { "min[%s_%.%-]?dam", "min[%s_%.%-]?dmg" }, exclude = {},
            ok = function(v) return type(v) == "number" and v >= 0 and v <= 300 end },
    safe = { tag = "SAFE", title = "Safepoint",
             patterns = { "safe[%s_%.%-]?point" },
             exclude = { "unsafe", "multi", "hitbox", "limit", "min" },
             ok = function(v) return type(v) == "boolean" or (type(v) == "number" and v >= 0 and v <= 10) end },
    baim = { tag = "BAIM", title = "Body-aim",
             patterns = { "body[%s_%.%-]?aim", "baim", "prefer[%s_%.%-]?body", "force[%s_%.%-]?body" },
             exclude = { "lethal", "disabl", "hp", "health", "dam", "dmg", "condition", "unsafe",
                         "after", "miss", "shot", "min", "max" },
             ok = function(v) return type(v) == "boolean" end },
    hitbox = { tag = "HITBOX", title = "Hitboxes",
               patterns = { "hit[%s_%.%-]?box" },
               exclude = { "point", "scale", "prior", "debug", "history", "backtrack" },
               ok = function(v) return type(v) == "table" end },
}
for i = 1, #ORDER_P do
    local sl = SL[ORDER_P[i]]
    sl.id, sl.recs, sl.n = ORDER_P[i], {}, 0
    sl.w, sl.g, sl.force, sl.custom, sl.live, sl.full = nil, 0, false, false, 0, false
end
local CLAIMED = {}       -- path -> parameter id: one path serves one parameter

SL.safe.transform = function(orig)
    if type(orig) == "boolean" then return true end
    if type(orig) == "number" then return SAFE_COMBO_VALUE end
    return nil
end
SL.baim.transform = function(orig)
    if type(orig) == "boolean" then return true end
    return nil
end
SL.hitbox.transform = function(orig) return strip_head(orig) end

-- Path tags: which weapon group a path belongs to. Untagged paths apply to every group.
local PATH_TAGS = {
    { 1, { "ssg", "scout" } },
    { 2, { "awp" } },
    { 3, { "autosnip", "auto[%s_%.%-]snip", "scar", "g3sg1", "%f[%w]auto%f[%W]" } },
    { 4, { "deagle", "revolver", "%f[%w]r8%f[%W]", "heavy" } },
    { 5, { "pistol" } },
    { 6, { "rifle", "smg", "shotgun", "machine", "%f[%w]other%f[%W]" } },
}

local function tags_for(low)
    local tags
    for i = 1, #PATH_TAGS do
        if any_match(low, PATH_TAGS[i][2]) then
            tags = tags or {}
            tags[PATH_TAGS[i][1]] = true
        end
    end
    if tags and tags[4] and tags[5] and s_find(low, "heavy", 1, true) then tags[5] = nil end
    return tags
end

function Bind.add_path(sl, path, forced)
    local owner = CLAIMED[path]
    if owner then
        if forced and owner ~= sl.id then
            say(sl.title .. ": path '" .. path .. "' is already used by '" .. SL[owner].title .. "'")
        end
        return false
    end
    local v = cfg_get(path)
    if v == nil then
        if forced then say(sl.title .. ": path '" .. path .. "' not found in config") end
        return false
    end
    if not sl.ok(v) then
        if forced then say(sl.title .. ": path '" .. path .. "' has an unsupported type (" .. type(v) .. ")") end
        return false
    end
    CLAIMED[path] = sl.id
    sl.n = sl.n + 1
    -- orig: user's value (NONE until touched); cur: what config holds now; want: last desired
    -- value; eff: whether config accepted it.
    sl.recs[sl.n] = { path = path, tags = tags_for(s_lower(path)), orig = NONE, cur = nil, want = nil,
                      eff = false, bad = 0, mism = 0, dead = false, warned = false, ro = false }
    return true
end

local function clear_pub()
    if RB.hc ~= nil or RB.dmg ~= nil or RB.safe or RB.baim ~= nil or RB.strict or RB.pub_thp ~= nil then
        RB.hc, RB.dmg, RB.safe, RB.baim, RB.strict, RB.pub_thp = nil, nil, false, nil, false, nil
        VIS.dirty = true
    end
end

local function rec_fail(sl, rec, why)
    rec.bad = rec.bad + 1
    if rec.bad < K.BAD_LIMIT then
        sl.force = true
    elseif not rec.dead then
        rec.dead = true
        say("path disabled until rescan (" .. why .. "): " .. rec.path)
    end
end

-- Returns the user's value. true = config is guaranteed to hold the original.
function Bind.restore(sl, rec, final)
    if rec.orig == NONE then return true end
    if rec.dead and not final then return false end
    if not same(rec.cur, rec.orig) then
        if not cfg_set(rec.path, rec.orig) then
            rec_fail(sl, rec, "restore failed, original stays in the journal")
            return false
        end
        if CFG.log_cfg then say(format("%s <- %s (restore)", rec.path, fmt_v(rec.orig))) end
    end
    rec.orig, rec.cur, rec.want, rec.eff = NONE, nil, nil, false
    Journal.remove(rec.path)
    return true
end

-- Restores everything. A journal entry disappears only together with a successful restore.
function Bind.release(final)
    clear_pub()
    if not RB.touched and not final then return end
    local pending = false
    for i = 1, #ORDER_P do
        local sl = SL[ORDER_P[i]]
        local recs = sl.recs
        for j = 1, sl.n do
            local rec = recs[j]
            if rec.orig ~= NONE and not Bind.restore(sl, rec, final) and not rec.dead then pending = true end
        end
        sl.w, sl.g, sl.force, sl.live = nil, 0, false, 0
    end
    RB.touched = pending
end

function Bind.scan()
    Bind.release(true)
    for k in pairs(CLAIMED) do CLAIMED[k] = nil end
    for i = 1, #ORDER_P do
        local sl = SL[ORDER_P[i]]
        sl.recs, sl.n, sl.w, sl.g, sl.force, sl.custom, sl.live, sl.full = {}, 0, nil, 0, false, false, 0, false
        local list = CUSTOM_PATHS[sl.id]
        if type(list) == "table" and #list > 0 then
            sl.custom = true
            for j = 1, #list do
                if type(list[j]) == "string" then Bind.add_path(sl, list[j], true) end
            end
        end
    end
    RB.eval_at = 0
    local ok, keys = pcall(config.keys)
    if not ok or type(keys) ~= "table" then
        say("config.keys unavailable: " .. tostring(keys) .. ". Fill CUSTOM_PATHS.")
        return false
    end
    for i = 1, #keys do
        local path = keys[i]
        if type(path) == "string" and not CLAIMED[path] then
            local low = s_lower(path)
            local excluded = nil
            for j = 1, #ORDER_P do
                local sl = SL[ORDER_P[j]]
                if not sl.custom and any_match(low, sl.patterns) then
                    if excluded == nil then excluded = any_match(low, GENERIC_EXCLUDE) end
                    if excluded then break end
                    if not any_match(low, sl.exclude) then
                        if sl.n < K.MAX_CANDS then
                            if Bind.add_path(sl, path, false) then break end
                        elseif not sl.full then
                            sl.full = true
                            say(format("%s: more than %d paths found, extras skipped. Use CUSTOM_PATHS.", sl.title, K.MAX_CANDS))
                        end
                    end
                end
            end
        end
    end
    return true
end

function Bind.total()
    local n = 0
    for i = 1, #ORDER_P do n = n + SL[ORDER_P[i]].n end
    return n
end

function Bind.summary()
    local p = {}
    for i = 1, #ORDER_P do
        local sl = SL[ORDER_P[i]]
        p[#p + 1] = format("%s %d", sl.tag, sl.n)
    end
    return tconcat(p, " · ")
end

function Bind.dump()
    say("---- config paths found by 0x ----")
    for i = 1, #ORDER_P do
        local sl = SL[ORDER_P[i]]
        say(format("%s: %d found%s", sl.title, sl.n, sl.custom and " (manual)" or ""))
        for j = 1, sl.n do
            local r = sl.recs[j]
            local tg = "all"
            if r.tags then
                local t = {}
                for g in pairs(r.tags) do t[#t + 1] = tostring(g) end
                tsort(t)
                tg = tconcat(t, ",")
            end
            say(format("   %s = %s  [weapon groups: %s]%s%s", r.path, fmt_v(cfg_get(r.path)), tg,
                       r.dead and "  DISABLED" or "", r.ro and "  READ-ONLY" or ""))
        end
    end
end

-- Original numeric value of the first matching path (Strict and damage cap).
function Bind.base(sl, group)
    if not group then return nil end
    for i = 1, sl.n do
        local r = sl.recs[i]
        if not r.dead and (r.tags == nil or r.tags[group]) then
            local v = r.orig
            if v == NONE then v = cfg_get(r.path) end
            if type(v) == "number" then return v end
        end
    end
    return nil
end

-- Writes the desired value (number / value / TRANSFORM). true = config holds it.
function Bind.push(sl, rec, target)
    if rec.dead then return false end
    if rec.orig == NONE then
        local cur = cfg_get(rec.path)
        if cur == nil then
            rec_fail(sl, rec, "path no longer readable")
            return false
        end
        local pending = Journal.data[rec.path]
        if pending ~= nil and type(pending) == type(cur) then
            rec.orig = copy(pending)              -- previous restore failed: the real original is in the journal
        else
            rec.orig = copy(cur)
            Journal.add(rec.path, rec.orig)
        end
        rec.cur, rec.want, rec.eff = copy(cur), nil, false
        RB.touched = true
    end

    local val, supported = target, true
    if target == TRANSFORM then
        val = sl.transform(rec.orig)
        if val == nil then
            if not rec.warned then
                rec.warned = true
                say("value format not supported, path skipped: " .. rec.path .. " = " .. fmt_v(rec.orig))
            end
            val, supported = rec.orig, false
        end
    end
    if rec.want ~= nil and same(rec.want, val) then return rec.eff end

    local eff
    if same(val, rec.orig) then
        if not same(rec.cur, rec.orig) then
            if not cfg_set(rec.path, rec.orig) then
                rec_fail(sl, rec, "write rejected")
                return false
            end
            if CFG.log_cfg then say(format("%s <- %s (equals yours)", rec.path, fmt_v(rec.orig))) end
            rec.cur = copy(rec.orig)
        end
        eff = supported
    elseif cfg_set(rec.path, val) then
        local echo = cfg_get(rec.path)             -- config may clamp or round the value
        if echo == nil then echo = val end
        rec.cur, rec.bad = copy(echo), 0
        eff = not same(echo, rec.orig)
        if not eff and not rec.ro then
            rec.ro = true
            say("write accepted but the value did not change: " .. rec.path .. " (wanted " .. fmt_v(val) .. ")")
        end
        if CFG.log_cfg then say(format("%s: %s -> %s", rec.path, fmt_v(rec.orig), fmt_v(echo))) end
    else
        rec_fail(sl, rec, "write rejected")
        return false
    end
    rec.want, rec.eff = copy(val), eff
    return eff
end

function Bind.apply(sl, want, group)
    if sl.n == 0 then return end
    if want == nil then group = 0 end
    if sl.w == want and sl.g == group and not sl.force then return end
    sl.w, sl.g, sl.force = want, group, false
    local recs, live = sl.recs, 0
    for i = 1, sl.n do
        local rec = recs[i]
        if want ~= nil and (rec.tags == nil or rec.tags[group]) then
            if Bind.push(sl, rec, want) then live = live + 1 end
        elseif rec.orig ~= NONE then
            Bind.restore(sl, rec, false)
        end
    end
    sl.live = live
end

-- Cross-check: a value changed by the user or by other code becomes the new original.
function Bind.verify()
    for i = 1, #ORDER_P do
        local sl = SL[ORDER_P[i]]
        local recs = sl.recs
        for j = 1, sl.n do
            local rec = recs[j]
            if rec.orig ~= NONE and not rec.dead then
                local cur = cfg_get(rec.path)
                if cur ~= nil then
                    if same(cur, rec.cur) then
                        rec.mism = 0
                    else
                        if not STATE.menu_open then rec.mism = rec.mism + 1 end
                        if rec.mism > K.MISM_LIMIT then
                            rec.dead = true
                            rec.orig, rec.cur, rec.want, rec.eff = NONE, nil, nil, false
                            Journal.remove(rec.path)
                            say("path disabled until rescan (constantly changed by other code): " .. rec.path)
                        else
                            rec.orig, rec.cur, rec.want, rec.eff = copy(cur), copy(cur), nil, false
                            Journal.add(rec.path, rec.orig)
                            sl.force = true
                        end
                    end
                end
            end
        end
    end
end

-- ---------------------------------------------------------------- logic
local HB = { cache = {}, n = 0 }
local CAND, CAND_N = {}, 0

local function clear_target()
    RB.t_hp, RB.t_air, RB.t_move, RB.t_name = nil, false, false, nil
    if RB.t_addr ~= nil then RB.t_addr, RB.baim_until = nil, 0 end
end

function RB.reset()
    HB.cache, HB.n = {}, 0
    for i = 1, CAND_N do CAND[i].pawn = nil end
    CAND_N = 0
    RB.waddr, RB.wgroup, RB.state = nil, nil, nil
    clear_target()
    RB.baim_reason, RB.baim_until = nil, 0
    RB.base_hc, RB.base_dmg = nil, nil
    RB.land_soon, RB.air_ticks = false, 0
    RB.eval_at = 0
    VIS.dirty = true
end

function RB.classify(w)
    local ok, info = pcall(w.weapon_info, w)
    if not ok or type(info) ~= "table" then return nil end
    if info.gun == false then return nil end
    local def = tonumber(info.def)
    if def and WPN_BY_DEF[def] then return WPN_BY_DEF[def] end
    if def and NON_GUN_DEF[def] then return nil end
    local name = type(info.name) == "string" and s_lower(info.name) or ""
    for i = 1, #WPN_BY_NAME do
        if s_find(name, WPN_BY_NAME[i][1], 1, true) then return WPN_BY_NAME[i][2] end
    end
    for i = 1, #NON_GUN do
        if s_find(name, NON_GUN[i], 1, true) then return nil end
    end
    return 6
end

function RB.weapon(lp)
    local w = lp:weapon()
    if not w then
        RB.wgroup, RB.waddr = nil, nil
        return
    end
    local addr = w:address()
    if addr ~= RB.waddr or RB.tick_n - RB.wtick >= K.WEAPON_TICKS then
        RB.waddr, RB.wtick = addr, RB.tick_n
        local g = RB.classify(w)
        if g ~= RB.wgroup then
            RB.wgroup = g
            RB.eval_at = 0
            VIS.dirty = true
        end
    end
end

-- Landing prediction: will we touch the ground within land_ticks ticks?
function RB.predict()
    local ok, sim = pcall(engine.simulate, CFG.land_ticks)
    if not ok or type(sim) ~= "table" then
        RB.sim_fail = RB.sim_fail + 1
        if RB.sim_fail >= 3 then
            RB.sim_fail = 0
            say("engine.simulate unavailable, air detection switched to 'Ground + vertical speed'")
            CFG.air_mode = 1
            RB.sync_mode = 1                     -- widget is updated from paint
        end
        return
    end
    RB.sim_fail = 0
    for i = 1, #sim do
        local s = sim[i]
        if type(s) == "table" and s.valid ~= false and (s.landed or s.on_ground) then
            RB.land_soon = true
            return
        end
    end
end

function RB.movement(lp, cmd)
    local vel = lp:velocity()
    local vx, vy, vz = 0, 0, 0
    if vel then vx, vy, vz = vel.x or 0, vel.y or 0, vel.z or 0 end
    local speed = sqrt(vx * vx + vy * vy)
    local grounded = lp:on_ground() ~= false
    if grounded then
        RB.air_ticks, RB.land_soon = 0, false
    else
        RB.air_ticks = RB.air_ticks + 1
    end
    local mode = CFG.air_mode
    local air = false
    if not grounded then
        if mode == 2 then
            air = true
        else
            air = RB.air_ticks >= 2 and (abs(vz) >= CFG.air_thr or RB.air_ticks >= 10)
        end
    end
    if air and mode == 3 then
        -- Simulated every tick; a 1-3 tick lead would otherwise be late. While rising, landing
        -- within land_ticks is impossible and the simulation is skipped.
        if not RB.land_soon and vz <= RB.g_tick * CFG.land_ticks + K.SIM_MARGIN then RB.predict() end
        if RB.land_soon then air = false end
    end
    local st
    if air then
        st = (CFG.apex_on and abs(vz) <= CFG.apex_win) and ST.APEX or ST.AIR
    elseif band(lp:flags() or 0, K.FL_DUCKING) ~= 0 then
        st = ST.DUCK
    elseif speed < K.MOVE_EPS then
        st = ST.STAND
    elseif cmd:has(K.BTN_SPEED) then
        st = ST.SLOW
    else
        st = ST.MOVE
    end
    STATE.lp_air = air
    STATE.lp_moving = speed >= K.MOVE_EPS
    if st ~= RB.state then
        RB.state = st
        VIS.dirty = true
    end
end

local function hg_from_name(s)
    if type(s) ~= "string" then return 0 end
    local l = s_lower(s)
    if s_find(l, "head", 1, true) then return K.HG_HEAD end
    if s_find(l, "chest", 1, true) then return K.HG_CHEST end
    if s_find(l, "stomach", 1, true) then return K.HG_STOMACH end
    return 0
end

-- Head / chest / stomach hitbox indices from pawn:hitboxes(), cached per pawn.
function RB.hitbox_ids(pawn)
    local addr = pawn:address()
    local c = HB.cache[addr]
    if c and RB.tick_n - c.t < K.HB_TTL then return c end
    local ok, list = pcall(pawn.hitboxes, pawn)
    if not ok or type(list) ~= "table" then return nil end
    local body, head, got = {}, nil, {}
    for i = 1, #list do
        local hb = list[i]
        if type(hb) == "table" and hb.index ~= nil then
            local g = hb.group
            if type(g) ~= "number" then g = hg_from_name(hb.group_name or g) end
            if g == K.HG_HEAD then
                if not head then head = { index = hb.index, group = g } end
            elseif (g == K.HG_CHEST or g == K.HG_STOMACH) and not got[g] then
                got[g] = true
                body[#body + 1] = { index = hb.index, group = g }
            end
        end
    end
    if c == nil then
        if HB.n >= K.HB_MAX then HB.cache, HB.n = {}, 0 end
        HB.n = HB.n + 1
    end
    c = { t = RB.tick_n, body = body, head = head }
    HB.cache[addr] = c
    return c
end

function RB.dmg_at(eye, pawn, entry)
    local pos = pawn:hitbox(entry.index)
    if not pos then return 0 end
    local ok, d = pcall(trace.damage, pawn, pos, entry.group, eye)
    if ok and type(d) == "number" then return d end
    return 0
end

function RB.eval_targets(lp)
    local grp = RB.wgroup
    RB.base_hc = Bind.base(SL.hc, grp)
    RB.base_dmg = Bind.base(SL.dmg, grp)

    local baim_ok = CFG.baim_on and (SL.baim.n + SL.hitbox.n) > 0
    local need_trace = baim_ok and (CFG.baim_lethal or CFG.baim_2x)
    local need_target = need_trace or (baim_ok and (CFG.baim_hp_on or CFG.baim_unres))
                        or (CFG.dmg_cap and SL.dmg.n > 0)
                        or ((CFG.hc_tgt_air ~= 0 or CFG.hc_tgt_move ~= 0 or CFG.unres_hc ~= 0) and SL.hc.n > 0)
    if not need_target then
        clear_target()
        RB.baim_reason = nil
        return
    end
    local eye, view = lp:eye_position(), engine.view_angles()
    if not eye or not view then
        clear_target()
        RB.baim_reason = nil
        return
    end

    local ex, ey, ez = eye.x, eye.y, eye.z - K.EYE_OFFSET
    local vp, vy, lim = view.x, view.y, CFG.baim_fov
    local players = entity.players()
    local n = 0
    if type(players) == "table" then
        for i = 1, #players do
            local p = players[i]
            local pawn = p and p.pawn
            if pawn and pawn:alive() and pawn:is_enemy() then
                local o = pawn:origin()
                if o then
                    local dx, dy, dz = o.x - ex, o.y - ey, o.z - ez
                    local dp = normalize(deg(atan2(-dz, sqrt(dx * dx + dy * dy))) - vp)
                    local dw = normalize(deg(atan2(dy, dx)) - vy)
                    local fov = sqrt(dp * dp + dw * dw)
                    if fov <= lim then
                        n = n + 1
                        local c = CAND[n]
                        if not c then
                            c = {}
                            CAND[n] = c
                        end
                        c.pawn, c.fov, c.hp, c.bd, c.hd = pawn, fov, 100, 0, 0
                    end
                end
            end
        end
    end
    for i = n + 1, CAND_N do CAND[i].pawn = nil end
    CAND_N = n

    local pick = nil
    for i = 1, min(n, K.MAX_TARGETS) do
        local m = i
        for j = i + 1, n do
            if CAND[j].fov < CAND[m].fov then m = j end
        end
        if m ~= i then CAND[i], CAND[m] = CAND[m], CAND[i] end
        local c = CAND[i]
        c.hp = c.pawn:health() or 100
        if need_trace then
            local ids = RB.hitbox_ids(c.pawn)
            if ids then
                local need = c.hp + CFG.baim_margin
                for j = 1, #ids.body do
                    local d = RB.dmg_at(eye, c.pawn, ids.body[j])
                    if d > c.bd then c.bd = d end
                    if d >= need then break end
                end
                if CFG.baim_2x and ids.head and c.bd > 0 and c.bd * 2 >= need
                   and not (CFG.baim_lethal and c.bd >= need) then
                    c.hd = RB.dmg_at(eye, c.pawn, ids.head)
                end
            end
        end
        if not pick then pick = c end
        if c.bd > 0 then
            pick = c
            break
        end
    end

    local reason = nil
    if pick then
        local p = pick.pawn
        local addr = p:address()
        if addr ~= RB.t_addr then RB.t_addr, RB.baim_until = addr, 0 end
        RB.t_hp = pick.hp
        RB.t_air = (p:on_ground() == false)
        local pv = p:velocity()
        RB.t_move = (pv ~= nil) and (pv.x * pv.x + pv.y * pv.y > K.T_MOVE_SQR)
        if baim_ok then
            local hp, bd = pick.hp, pick.bd
            local need = hp + CFG.baim_margin
            if CFG.baim_lethal and bd > 0 and bd >= need then
                reason = "LETHAL"
            elseif CFG.baim_2x and bd > 0 and bd * 2 >= need and pick.hd < hp then
                reason = "2X"
            elseif CFG.baim_hp_on and hp <= CFG.baim_hp then
                reason = "HP"
            end
        end
    else
        clear_target()
    end

    if reason then
        RB.baim_reason, RB.baim_until = reason, RB.tick_n + K.HOLD_TICKS
    elseif RB.tick_n > RB.baim_until then
        RB.baim_reason = nil
    end
end

local function set_pub(k, v)
    if RB[k] ~= v then
        RB[k] = v
        VIS.dirty = true
    end
end

function RB.decide(grp)
    local st = RB.state
    local airborne = (st == ST.AIR or st == ST.APEX)
    local strict, kbaim, kdmg = bind_on(UI.k_strict), bind_on(UI.k_baim), bind_on(UI.k_dmg)
    if not CFG.baim_on then RB.baim_reason = nil end

    -- resolver synergy: how much do we trust the guess for the crosshair target?
    local trec = RB.t_addr and RES.by_pawn[RB.t_addr] or nil
    local unres = (trec ~= nil) and CFG.enable and RES.unresolved(trec)
    RB.t_unres = unres

    -- hitchance
    local hc = nil
    if airborne then
        if CFG.air_on then
            hc = (st == ST.APEX and CFG.apex_on) and CFG.apex_hc or CFG.air_hc
        end
    elseif CFG.hc_on then
        local v
        if st == ST.STAND then v = CFG.hc_stand
        elseif st == ST.SLOW then v = CFG.hc_slow
        elseif st == ST.MOVE then v = CFG.hc_move
        else v = CFG.hc_duck end
        if v and v > 0 then hc = v end
    end
    if hc and RB.t_hp then
        if RB.t_air then hc = hc + CFG.hc_tgt_air end
        if RB.t_move then hc = hc + CFG.hc_tgt_move end
    end
    if unres and CFG.unres_hc ~= 0 then
        if not hc then hc = RB.base_hc end
        if hc then hc = hc + CFG.unres_hc end
    end
    if strict then
        if not hc then hc = RB.base_hc end
        if hc then hc = hc + CFG.strict_bonus end
    end
    if hc then hc = clamp(round(hc), 1, 100) end

    -- min damage
    local dmg = nil
    if airborne and CFG.air_on then dmg = CFG.air_dmg end
    if kdmg then dmg = CFG.dmg_bind_val end
    if CFG.dmg_cap and RB.t_hp then
        local base = dmg or RB.base_dmg
        if base and base <= 100 and RB.t_hp < base then dmg = max(1, RB.t_hp) end
    end
    if dmg then dmg = clamp(round(dmg), 1, 130) end

    -- safepoint and body-aim
    local want_safe_b = (airborne and CFG.air_on and CFG.air_safe) or strict
    local baim = nil
    if kbaim then
        baim = "KEY"
    elseif RB.baim_reason then
        baim = RB.baim_reason
    elseif unres and CFG.baim_on and CFG.baim_unres then
        baim = "RES"
    end

    local want_safe = want_safe_b and TRANSFORM or nil
    local want_baim = baim and TRANSFORM or nil
    Bind.apply(SL.hc, hc, grp)
    Bind.apply(SL.dmg, dmg, grp)
    Bind.apply(SL.safe, want_safe, grp)
    Bind.apply(SL.baim, want_baim, grp)
    Bind.apply(SL.hitbox, want_baim, grp)

    -- the panel shows only what is really written into the ragebot
    local hc_live, safe_live = SL.hc.live > 0, SL.safe.live > 0
    set_pub("hc", hc_live and hc or nil)
    set_pub("dmg", (SL.dmg.live > 0) and dmg or nil)
    set_pub("safe", (want_safe_b and safe_live) and true or false)
    set_pub("baim", (SL.baim.live + SL.hitbox.live > 0) and baim or nil)
    set_pub("strict", (strict and (hc_live or safe_live)) and true or false)
    set_pub("pub_thp", RB.t_hp)
end

-- Not active this tick: restore the ragebot values; the panel hides the state.
function RB.stand_down(keep_state)
    if not keep_state and RB.state ~= nil then
        RB.state = nil
        VIS.dirty = true
    end
    RB.eval_at = 0
    Bind.release(false)
end

function RB.set_status(txt)
    if UI.rb_status and not UI.rb_status.dummy then pcall(UI.rb_status.set, UI.rb_status, "Paths: " .. txt) end
end

function ACT.rescan()
    local ok = Bind.scan()
    local txt = ok and Bind.summary() or "config.keys unavailable"
    RB.set_status(txt)
    notify("Found: " .. txt)
end

function ACT.dump() Bind.dump() end

-- Per-tick entry point (createmove).
function RB.tick(cmd)
    local now = STATE.rt
    RB.cm_t = now
    RB.tick_n = RB.tick_n + 1

    if not CFG.rb_enable then
        if RB.paused then RB.paused, VIS.dirty = false, true end
        RB.stand_down(false)
        return
    end
    if STATE.menu_open and CFG.pause_menu then
        if not RB.paused then RB.paused, VIS.dirty = true, true end
        RB.stand_down(true)
        return
    end
    if RB.paused then RB.paused, VIS.dirty = false, true end

    local lp = entity.local_pawn()
    if not lp or not lp:alive() then
        if RB.state ~= nil then RB.reset() end
        RB.stand_down(false)
        return
    end

    RB.weapon(lp)
    local grp = RB.wgroup
    if not grp or not multi_on(CFG.weapons, grp, WPN_ITEMS) then
        RB.stand_down(false)
        return
    end

    RB.movement(lp, cmd)
    if RB.tick_n >= RB.eval_at then
        RB.eval_at = RB.tick_n + K.EVAL_TICKS
        RB.eval_targets(lp)
    end
    RB.decide(grp)
    if RB.tick_n % K.VERIFY_TICKS == 0 then Bind.verify() end
end

-- Once per second: everything that does not have to happen every frame.
function RB.housekeeping(now)
    RB.hk_t = now
    local ok, ig = pcall(engine.in_game)
    RB.in_game = (not ok) or ig ~= false
    local sw, sh = render.screen_size()
    if type(sw) == "number" and type(sh) == "number" and sw > 0 and sh > 0 then STATE.sw, STATE.sh = sw, sh end
    if SET.dirty and now - SET.dirty_t >= K.SAVE_DELAY then
        if settings_save() then SET.dirty = false else SET.dirty_t = now + K.IO_RETRY end
    end
    Journal.flush(false)
    if STATE.strikes > 0 and now - STATE.strike_t > K.ERR_FORGIVE then STATE.strikes = 0 end
end

-- Background tasks run from paint; createmove takes over if paint goes silent.
function RB.background(now)
    if RB.sync_mode then
        if REG.air_mode then write_el(REG.air_mode, RB.sync_mode) end
        RB.sync_mode = false
    end
    cfg_tick(false)
    -- menu_toggled can be missed: cross-check with input.menu_open after a short grace period
    if now - STATE.menu_evt_t > 0.25 and now - STATE.menu_poll_t > 0.25 then
        STATE.menu_poll_t = now
        local ok, open = pcall(input.menu_open)
        if ok and type(open) == "boolean" and open ~= STATE.menu_open then
            STATE.menu_open = open
            MENU.last = -1e9
        end
    end
    if Journal.add_dirty then Journal.flush(false) end
    if now - RB.hk_t >= K.HK_INTERVAL then RB.housekeeping(now) end
end

function RB.on_menu_toggled(open)
    STATE.menu_open = open and true or false
    STATE.menu_evt_t = STATE.rt
    MENU.last = -1e9                             -- re-read the menu on the next frame
    if STATE.menu_open then
        if CFG.pause_menu and CFG.rb_enable then
            RB.paused, VIS.dirty = true, true
            Bind.release(false)
        end
        Journal.flush(true)
    end
end

function RB.on_level()
    Bind.release(true)
    RB.reset()
    Journal.flush(true)
end

function RB.on_unload()
    Bind.release(true)
    Journal.flush(true)
end

-- ============================================================================
--  VISUALS
-- ============================================================================
VIS.font, VIS.ver = nil, "v" .. META.version
VIS.feed = {}
VIS.dirty, VIS.a, VIS.paused, VIS.focus_key, VIS.rebuilt_t = true, 0, nil, nil, 0
VIS.rows, VIS.nrows = {}, 0
VIS.size, VIS.w, VIS.h, VIS.pad, VIS.rh, VIS.th, VIS.tw = 0, 0, 0, 10, 18, 14, 14
VIS.memo, VIS.memo_n = {}, 0
VIS.drag, VIS.px, VIS.py, VIS.was_down = nil, nil, nil, false
VIS.panel_x, VIS.panel_y, VIS.panel_bottom = nil, nil, nil

local IND_KEYS = { "MODE", "HC", "DMG", "SAFE", "BAIM", "STRICT", "TARGET", "AA", "YAW", "CONF", "PITCH", "HITS" }
local IND_VALS = { "PAUSE", "100%", "130", "ON", "LETHAL", "100 HP", "JITTER L", "+180°", "FLICK", "99/99" }

function VIS.init()
    local ok, f = pcall(render.font, "Segoe UI", 13)
    if ok and f then
        local ok2, loaded = pcall(f.loaded, f)
        if ok2 and loaded then VIS.font = f end
    end
end

function VIS.text(x, y, col, str, size)
    if VIS.font then
        render.text(x, y, col, str, "", size, VIS.font)
    else
        render.text(x, y, col, str, "", size)
    end
end

function VIS.measure(str, size)
    local ok, w, h
    if VIS.font then
        ok, w, h = pcall(render.text_size, str, "", size, VIS.font)
    else
        ok, w, h = pcall(render.text_size, str, "", size)
    end
    if ok and type(w) == "number" then return w, (type(h) == "number") and h or size end
    return utf8_len(str) * size * 0.55, size
end

local function text_w(str)
    local w = VIS.memo[str]
    if not w then
        if VIS.memo_n >= K.MEMO_MAX then VIS.memo, VIS.memo_n = {}, 0 end
        w = VIS.measure(str, VIS.size)
        VIS.memo[str] = w
        VIS.memo_n = VIS.memo_n + 1
    end
    return w
end

-- Event feed entry (hit / body / miss / kill / info).
function VIS.push(kind, text)
    local feed = VIS.feed
    feed[#feed + 1] = { kind = kind, text = text, t = globals.realtime() }
    if #feed > C.FEED_MAX then tremove(feed, 1) end
end

local function make_pal(r, g, b, qa)
    local k = qa / 255
    return {
        bg = color(10, 11, 17, floor(214 * k)), line = color(255, 255, 255, floor(24 * k)),
        acc = color(r, g, b, qa), acc_dim = color(r, g, b, floor(70 * k)),
        key = color(122, 126, 146, qa), val = color(236, 238, 246, qa),
        good = color(120, 220, 160, qa), warn = color(255, 190, 96, qa), bad = color(255, 110, 110, qa),
        _r = r, _g = g, _b = b, _qa = qa,
    }
end

-- Palettes are rebuilt only when the accent or the alpha changes.
function VIS.palette(slot, qa)
    local acc = CFG.accent
    local r, g, b = 140, 148, 255
    if type(acc) == "table" and type(acc.r) == "number" and type(acc.g) == "number" and type(acc.b) == "number" then
        r, g, b = acc.r, acc.g, acc.b
    end
    local p = VIS[slot]
    if p and p._r == r and p._g == g and p._b == b and p._qa == qa then return p end
    p = make_pal(r, g, b, qa)
    VIS[slot] = p
    return p
end

-- ---------------------------------------------------------------- overlay
local function side_label(rec) return (rec.pred_side > 0) and "L" or "R" end

function VIS.overlay(rt, P)
    local detailed = (CFG.ov_style == 2)
    local focus = RES.focus
    for _, rec in pairs(RES.records) do
        if rec.pawn and rec.resolved and rt - rec.seen_rt < 0.1 then
            local ok, l, t, r = pcall(rec.pawn.bbox, rec.pawn)
            if ok and type(l) == "number" and type(t) == "number" and type(r) == "number" then
                local col = rec.applied and P.val or P.key
                local dlt = normalize(rec.resolved_yaw - rec.raw_yaw)
                local txt = format("%s %s %d°", MODE_LABEL[rec.mode] or "?", side_label(rec), round(abs(dlt)))
                local w = render.text_size(txt)
                local cx = (l + r) * 0.5
                local y = t - (detailed and 30 or 16)
                render.text(cx - w * 0.5, y, col, txt)
                if detailed then
                    local sub = format("%d/%d · b%d%s", rec.hits, rec.misses, rec.brute_idx,
                        rec.pitch_kind ~= "" and (" · " .. rec.pitch_kind) or "")
                    local sw = render.text_size(sub)
                    render.text(cx - sw * 0.5, y + 13, P.key, sub)
                    local bw = clamp(r - l, 24, 60)
                    local bx = cx - bw * 0.5
                    render.rect_filled(bx, t - 3, bw, 2, P.acc_dim)
                    render.rect_filled(bx, t - 3, max(1, floor(bw * clamp(rec.conf, 0, 1))), 2, P.acc)
                end
                if rec == focus then
                    render.rect_filled(cx - w * 0.5, y + 12, w, 1, P.acc)
                end
            end
        end
    end
end

-- Short lines from the head: received yaw (dim) and resolved yaw (accent).
function VIS.yaw_lines(rt, P)
    for _, rec in pairs(RES.records) do
        if rec.pawn and rec.resolved and rt - rec.seen_rt < 0.1 then
            local head = safe(rec.pawn.eye_position, rec.pawn) or rec.en_eye
            if head then
                local sx, sy = render.world_to_screen(head)
                if sx then
                    local a = rad(rec.raw_yaw)
                    local tx, ty = render.world_to_screen(vector(head.x + cos(a) * 18, head.y + sin(a) * 18, head.z))
                    if tx then render.line(sx, sy, tx, ty, P.key, 1) end
                    a = rad(rec.resolved_yaw)
                    tx, ty = render.world_to_screen(vector(head.x + cos(a) * 26, head.y + sin(a) * 26, head.z))
                    if tx then render.line(sx, sy, tx, ty, rec.applied and P.acc or P.acc_dim, 2) end
                    render.circle_filled(sx, sy, 2, P.acc, 10)
                end
            end
        end
    end
end

-- ---------------------------------------------------------------- status panel
function VIS.layout(size)
    VIS.size, VIS.memo, VIS.memo_n = size, {}, 0
    local kw, vw = 0, 0
    for i = 1, #IND_KEYS do kw = max(kw, text_w(IND_KEYS[i])) end
    for i = 1, #IND_VALS do vw = max(vw, text_w(IND_VALS[i])) end
    for i = 1, #ST_NAME do vw = max(vw, text_w(ST_NAME[i])) end
    local pad = floor(size * 0.8)
    local tw, th = VIS.measure("0x", size + 2)
    local vwid = VIS.measure(VIS.ver, size - 2)
    VIS.pad, VIS.rh, VIS.th, VIS.tw = pad, floor(size * 1.55), th, tw
    VIS.w = max(pad * 2 + kw + 18 + vw, pad * 2 + tw + 6 + vwid + 40, floor(size * 13))
end

local function put_row(i, k, value, kind, frac)
    local r = VIS.rows[i]
    if not r then
        r = {}
        VIS.rows[i] = r
    end
    r[1], r[2], r[3], r[4], r[5] = k, value, kind, text_w(value), frac
    return i + 1
end

function VIS.rebuild(rb_show, rec)
    local n = 1
    if rb_show then
        n = put_row(n, "MODE", RB.paused and "PAUSE" or (RB.state and ST_NAME[RB.state] or "—"), 1)
        if RB.hc then n = put_row(n, "HC", RB.hc .. "%", 1) end
        if RB.dmg then n = put_row(n, "DMG", tostring(RB.dmg), 1) end
        if RB.safe then n = put_row(n, "SAFE", "ON", 2) end
        if RB.baim then n = put_row(n, "BAIM", RB.baim, 3) end
        if RB.strict then n = put_row(n, "STRICT", "ON", 2) end
        if RB.pub_thp then n = put_row(n, "TARGET", RB.pub_thp .. " HP", 1) end
    end
    if rec then
        n = put_row(n, "AA", (MODE_LABEL[rec.mode] or "?") .. " " .. side_label(rec), rec.applied and 2 or 1)
        n = put_row(n, "YAW", format("%+d°", round(normalize(rec.resolved_yaw - rec.raw_yaw))), 1)
        if rec.pitch_kind ~= "" then n = put_row(n, "PITCH", rec.pitch_kind, 3) end
        n = put_row(n, "CONF", format("%d%%", round(rec.conf * 100)), 4, rec.conf)
        n = put_row(n, "HITS", format("%d/%d", rec.hits, rec.misses), 1)
    end
    VIS.nrows = n - 1
    VIS.h = VIS.pad * 2 + VIS.th + 8 + VIS.nrows * VIS.rh + ((rb_show and RB.hc) and 8 or 0)
end

local function commit_drag(w, h)
    local nx = clamp(round(VIS.px / max(1, STATE.sw - w) * 100), 0, 100)
    local ny = clamp(round(VIS.py / max(1, STATE.sh - h) * 100), 0, 100)
    if REG.panel_x then write_el(REG.panel_x, nx) end
    if REG.panel_y then write_el(REG.panel_y, ny) end
    CFG.panel_x, CFG.panel_y = nx, ny
    VIS.drag, VIS.px, VIS.py = nil, nil, nil
    SET.dirty, SET.dirty_t = true, STATE.rt
end

-- Panel position; draggable with the left mouse button while the menu is open.
function VIS.position(w, h)
    local x = floor((STATE.sw - w) * CFG.panel_x / 100)
    local y = floor((STATE.sh - h) * CFG.panel_y / 100)
    if STATE.menu_open then
        local ok, mx, my = pcall(input.cursor)
        local down = safe(input.key_down, 1) == true
        if ok and type(mx) == "number" and type(my) == "number" then
            if VIS.drag then
                if down then
                    VIS.px, VIS.py = mx - VIS.drag.dx, my - VIS.drag.dy
                else
                    commit_drag(w, h)
                end
            elseif down and not VIS.was_down and mx >= x and mx <= x + w and my >= y and my <= y + h then
                VIS.drag = { dx = mx - x, dy = my - y }
                VIS.px, VIS.py = x, y
            end
        end
        VIS.was_down = down
    else
        if VIS.drag then commit_drag(w, h) end
        VIS.was_down = false
    end
    if VIS.px then return VIS.px, VIS.py end
    return x, y
end

function VIS.panel(rt)
    local rb_show = CFG.rb_enable and (RB.state ~= nil or RB.paused)
    local rec = CFG.enable and RES.focus or nil
    if rec and (not rec.resolved or rt - rec.seen_rt > 0.5) then rec = nil end
    local show = (rb_show or rec ~= nil) and RB.in_game
    local a = VIS.a
    if not show and a == 0 then return end
    a = a + ((show and 1 or 0) - a) * min(1, globals.frametime() * 10)
    if a < 0.02 then
        VIS.a = show and a or 0
        return
    end
    VIS.a = a
    if STATE.sw <= 0 or STATE.sh <= 0 then return end

    local size = round(13 * CFG.panel_scale / 100)
    if size ~= VIS.size then
        VIS.layout(size)
        VIS.dirty = true
    end
    local rkey = rec and rec.key or nil
    if VIS.dirty or RB.paused ~= VIS.paused or rkey ~= VIS.focus_key or (rec and rt - VIS.rebuilt_t > 0.1) then
        VIS.rebuild(rb_show, rec)
        VIS.paused, VIS.focus_key, VIS.dirty, VIS.rebuilt_t = RB.paused, rkey, false, rt
    end

    local P = VIS.palette("pal_panel", round(a * 255))
    local w, h, pad = VIS.w, VIS.h, VIS.pad
    local x, y = VIS.position(w, h)

    render.rect_filled(x, y, w, h, P.bg, 7)
    render.rect(x, y, w, h, P.line, 7, 1)
    render.rect_filled(x + 1, y + 10, 2, h - 20, P.acc, 1)
    VIS.text(x + pad, y + pad - 1, P.acc, "0x", size + 2)
    VIS.text(x + pad + VIS.tw + 6, y + pad + 1, P.key, VIS.ver, size - 2)
    local ry = y + pad + VIS.th + 8
    render.line(x + pad, ry - 4, x + w - pad, ry - 4, P.line, 1)
    for i = 1, VIS.nrows do
        local row = VIS.rows[i]
        local col = P.val
        if row[3] == 2 then col = P.good elseif row[3] == 3 then col = P.warn end
        VIS.text(x + pad, ry, P.key, row[1], size)
        if row[3] == 4 then
            local bw = floor(w * 0.32)
            local bx = x + w - pad - row[4] - 6 - bw
            local by = ry + floor(size * 0.5)
            render.rect_filled(bx, by, bw, 3, P.acc_dim, 1)
            render.rect_filled(bx, by, max(2, floor(bw * clamp(row[5] or 0, 0, 1))), 3, P.acc, 1)
        end
        VIS.text(x + w - pad - row[4], ry, col, row[2], size)
        ry = ry + VIS.rh
    end
    if rb_show and RB.hc then
        local bw = w - pad * 2
        render.rect_filled(x + pad, y + h - 9, bw, 3, P.acc_dim, 1)
        render.rect_filled(x + pad, y + h - 9, max(2, floor(bw * RB.hc / 100)), 3, P.acc, 1)
    end
    VIS.panel_x, VIS.panel_y, VIS.panel_bottom = x, y, y + h
end

-- ---------------------------------------------------------------- event feed
function VIS.feed_draw(rt, P)
    local feed = VIS.feed
    while #feed > 0 and rt - feed[1].t > C.FEED_LIFE do tremove(feed, 1) end
    if #feed == 0 then return end
    local size = round(12 * CFG.panel_scale / 100)
    local x, y
    if VIS.a > 0.02 and VIS.panel_x then
        x, y = VIS.panel_x, VIS.panel_bottom + 8
    else
        x = floor((STATE.sw - 200) * CFG.panel_x / 100)
        y = floor((STATE.sh - 100) * CFG.panel_y / 100)
    end
    for i = 1, #feed do
        local e = feed[i]
        local left = C.FEED_LIFE - (rt - e.t)
        local a = clamp(left, 0, 1)
        local col = P.val
        if e.kind == "hit" then col = P.good
        elseif e.kind == "miss" then col = P.warn
        elseif e.kind == "kill" then col = P.acc
        elseif e.kind == "info" then col = P.key end
        VIS.text(x + 2, y, col:alpha(floor(col.a * a)), e.text, size)
        y = y + size + 4
    end
end

-- ---------------------------------------------------------------- debug
function VIS.debug(rt, P)
    local x, y = 24, 120
    local rows = {}
    rows[#rows + 1] = format("%s v%s  insecure=%s write=%s simtime=%s body=%s pending=%d focus=%s",
        META.name, META.version, tostring(RES.insecure), tostring(RES.write_ok), tostring(RES.simtime_ok),
        tostring(RES.body_ok), #RES.pending, RES.focus and tostring(RES.focus.name) or "-")
    rows[#rows + 1] = format("ragebot: on=%s state=%s grp=%s hc=%s dmg=%s safe=%s baim=%s unres=%s paths=%s touched=%s",
        tostring(CFG.rb_enable), RB.state and ST_NAME[RB.state] or "-", tostring(RB.wgroup), tostring(RB.hc),
        tostring(RB.dmg), tostring(RB.safe), tostring(RB.baim), tostring(RB.t_unres), Bind.summary(), tostring(RB.touched))
    for _, rec in pairs(RES.records) do
        if rt - rec.seen_rt < 1 then
            local m = RES.brute_entry(rec)
            rows[#rows + 1] = format(
                "%-14s %-6s side=%s conf=%.2f score=%+.2f brute=%d(%+.2f) body=%+d fs=%+d mv=%+.1f md=%+d ab=%d amt=%d res=%d raw=%d p=%s h/m=%d/%d%s",
                tostring(rec.name):sub(1, 14), MODE_LABEL[rec.mode] or "?", side_label(rec), rec.conf, rec.score,
                rec.brute_idx, m, round(rec.body_delta), rec.fs_hint, rec.mv_hint, rec.md_hint, rec.ab_score,
                round(rec.amount), round(rec.resolved_yaw), round(rec.raw_yaw), rec.pitch_kind ~= "" and rec.pitch_kind or "-",
                rec.hits, rec.misses, rec.applied and "" or " [track]")
        end
    end
    local wmax = 0
    for i = 1, #rows do
        local w = render.text_size(rows[i])
        if w > wmax then wmax = w end
    end
    render.rect_filled(x - 8, y - 6, wmax + 16, #rows * 15 + 12, color(12, 12, 14, 200), 4)
    for i = 1, #rows do
        render.text(x, y + (i - 1) * 15, i <= 2 and P.acc or P.key, rows[i])
    end
end

-- ---------------------------------------------------------------- stats label (1 Hz)
function VIS.stats(rt)
    if rt - STATE.last_label < 1 then return end
    STATE.last_label = rt
    local tracked = 0
    for _, rec in pairs(RES.records) do
        if rt - rec.seen_rt < 1 then tracked = tracked + 1 end
    end
    if UI.stats and not UI.stats.dummy then
        pcall(UI.stats.set, UI.stats, format("tracked %d · shots %d · hits %d · misses %d · write %s",
            tracked, RES.total_shots, RES.total_hits, RES.total_misses,
            RES.write_ok == true and "on" or (RES.write_ok == false and "off" or "n/a")))
    end
end

function VIS.paint()
    local rt = STATE.rt
    VIS.stats(rt)
    if not CFG.enable and not CFG.rb_enable then
        VIS.a = 0
        return
    end
    local P = VIS.palette("pal_full", 255)
    if CFG.enable and RB.in_game then
        if CFG.overlay then VIS.overlay(rt, P) end
        if CFG.yaw_lines then VIS.yaw_lines(rt, P) end
    end
    if CFG.panel then VIS.panel(rt) else VIS.a = 0 end
    if CFG.feed and RB.in_game then VIS.feed_draw(rt, P) end
    if CFG.debug and CFG.enable then VIS.debug(rt, P) end
end

-- ============================================================================
--  LIFECYCLE
-- ============================================================================
local EVENTS = {}

-- A burst of errors: ragebot values are restored, the script pauses and tries again.
-- Only after ERR_STRIKES suspensions in a row does it stop until Save & Reload.
local function trip(name)
    STATE.strikes, STATE.strike_t = STATE.strikes + 1, STATE.rt
    pcall(Bind.release, true)
    pcall(RB.reset)
    pcall(Journal.flush, true)
    RB.paused = false
    if STATE.strikes >= K.ERR_STRIKES then
        STATE.failed = true
        notify("Too many errors in '" .. name .. "': 0x stopped, ragebot values restored. Fix the cause and Save & Reload.")
    else
        STATE.suspend_until = STATE.rt + K.ERR_COOLDOWN
        notify(format("Errors in '%s': 0x suspended for %d s, ragebot values restored.", name, K.ERR_COOLDOWN))
    end
end

-- Every callback error is caught here and never reaches the game.
local function guard(name, fn)
    return function(a, b, c)
        if STATE.failed and name ~= "unload" then return end
        STATE.rt = globals.realtime()
        if STATE.suspend_until then
            if STATE.rt < STATE.suspend_until then return end
            STATE.suspend_until = nil
        end
        local ok, err = pcall(fn, a, b, c)
        if ok then
            STATE.errs[name] = 0
            return
        end
        report(name, err)
        local n = (STATE.errs[name] or 0) + 1
        STATE.errs[name] = n
        if n >= K.ERR_LIMIT then
            STATE.errs[name] = 0
            trip(name)
        end
    end
end

local function hook(name, fn)
    EVENTS[#EVENTS + 1] = events.on(name, guard(name, fn))
end

-- Createmove: capture the angles actually sent (silent aim aware), run the ragebot assist.
local function on_createmove(cmd)
    local a = safe(cmd.view_angles, cmd)
    if a then STATE.cmd_angles = vector(a.x, a.y, 0) end
    local lp = entity.local_pawn()
    if lp then STATE.lp_air = (safe(lp.on_ground, lp) == false) end
    if STATE.rt - RB.paint_t > K.PAINT_TIMEOUT then RB.background(STATE.rt) end
    RB.tick(cmd)
end

local function on_paint()
    local now = STATE.rt
    RB.paint_t = now
    RB.background(now)
    -- createmove went silent (left the server, stalled simulation): never keep our overrides.
    if now - RB.cm_t > K.CM_TIMEOUT and (RB.touched or RB.state ~= nil or RB.paused) then
        RB.paused = false
        Bind.release(false)
        RB.reset()
    end
    VIS.paint()
end

local function on_level_init()
    RES.on_level_init()
    RB.on_level()
end

local function on_level_shutdown()
    RES.on_level_shutdown()
    RB.on_level()
end

local function boot()
    STATE.rt = globals.realtime()
    local ok_dt, dt = pcall(globals.interval)
    if ok_dt and type(dt) == "number" and dt > 0 then RB.g_tick = K.GRAVITY * dt end
    local sw, sh = render.screen_size()
    if type(sw) == "number" and type(sh) == "number" then STATE.sw, STATE.sh = sw, sh end

    VIS.init()
    build_menu()

    local restored = Journal.restore()
    local scanned = Bind.scan()                  -- before the first config read: status is ready at once
    RB.boot_status = scanned and Bind.summary() or "config.keys unavailable"
    RB.set_status(RB.boot_status)

    settings_load()
    cfg_tick(true)
    SET.dirty = false

    RES.store_load()
    RES.insecure = safe(client.insecure) == true
    STATE.insecure = RES.insecure
    local ok, open = pcall(input.menu_open)
    STATE.menu_open = ok and open == true

    hook("frame_stage",    RES.frame)
    hook("createmove",     on_createmove)
    hook("paint",          on_paint)
    hook("weapon_fire",    RES.on_weapon_fire)
    hook("player_hurt",    RES.on_player_hurt)
    hook("player_death",   RES.on_player_death)
    hook("round_start",    RES.on_round_start)
    hook("menu_toggled",   RB.on_menu_toggled)
    hook("level_init",     on_level_init)
    hook("level_shutdown", on_level_shutdown)

    events.on("unload", function()
        STATE.rt = globals.realtime()
        safe(RB.on_unload)
        safe(RES.store_save)
        if SET.dirty then safe(settings_save) end
        for i = 1, #EVENTS do safe(events.off, EVENTS[i]) end
        say("unloaded")
    end)

    if restored > 0 then notify("Restored " .. restored .. " ragebot values after a crash") end
    local cb = MENU.combo_base
    say(format("v%s loaded · insecure=%s · paths: %s · combo base: %s", META.version, tostring(STATE.insecure),
        RB.boot_status, cb == 0 and "0" or (cb == 1 and "1" or "by name")))
    if scanned and Bind.total() == 0 then
        notify("No ragebot paths found in config. Use 'Dump paths to console' on the 0x Ragebot tab.")
    else
        notify(format("%s v%s loaded · %s", META.name, META.version, META.credits))
    end
end

local boot_ok, boot_err = pcall(boot)
if not boot_ok then
    STATE.failed = true
    pcall(Bind.release, true)
    say("boot error: " .. tostring(boot_err))
end
