-- @author 0x
-- @uid 0

-- ============================================================================
--  0x  ·  v4.2  ·  resolver + rage assist + anti-aim + tetris
--  Neverlose CS2 Lua  ·  API: github.com/PbLJk/neverlose-lua-api
--
--  Credits: @kukluxk · @likvidatorchaes (subcult)
--
--  FILE MAP (search for the banner)
--    Fast paths / constants / shared state
--    MENU        registry, fault-tolerant constructors, layout (BUILD.*), snapshot, IO
--    RESOLVER    records, history, classification, hints, decision, shot feedback
--    RAGE ASSIST journal, config binding, movement state, targets, headshot assist, decision
--    VISUALS     overlay, yaw lines, status panel, event feed, debug, native ESP flag
--    ANTI-AIM    builder, modifiers, reactions, presets
--    TETRIS      rules, input, drawing, records
--    LIFECYCLE   guards, hooks, boot
--  Adding a module: create its table next to RES / RB / AA / TET, add a BUILD.<tab>() with
--  its widgets (W.chk / W.sld / W.cmb ... register the id for snapshots automatically), read
--  values from CFG.<id>, and hook its handlers in LIFE.boot with hook(event, tag, fn).
--
--  RESOLVER
--    Per-netupdate yaw / pitch history -> AA class (static / sway / jitter / spin / random),
--    body-yaw, freestanding and movement hints, lag-compensation watch, shot feedback with
--    classified misses, bruteforce cycling, persistence per SteamID, jitter phase prediction,
--    hint reliability learning.
--    4.2: two-cluster jitter model (2-means, tightness-weighted confidence), side memory per
--    AA class, blacklist of offsets that just missed, continuous trust score.
--  RAGE ASSIST
--    Reads and writes your ragebot through config.get / config.set. Paths are discovered
--    from config.keys; originals are journaled (db) and restored on disable, pause, death,
--    weapon change, map change, crash recovery and unload.
--    4.2: headshot assist - trusted target + better head damage -> head-only hitboxes,
--    hitchance bonus and an optional min-damage gate above the body damage.
--  ANTI-AIM
--    Condition builder (shared / standing / walking / running / ducking / air / duck-moving /
--    air-duck) with pitch, yaw base, offset, left / right add and a yaw modifier (jitter,
--    3-way, 5-way, spin, sway, random, skitter, flick), random switch delay, manual binds,
--    freestanding, edge yaw, safe head, anti-backstab, shuffle-when-hit, anti-bruteforce and
--    ten full presets. Angles are written with cmd:set_view_angles in createmove.
--  VISUALS
--    Player overlay, yaw lines, draggable status panel, event feed, debug panel with callback
--    timings, optional native ESP flag, anti-aim arrows.
--  TETRIS
--    Guideline Tetris in its own tab (floating window or embedded canvas).
--  CONFIG EXCHANGE
--    Export: data\db\0x_export.json (+ console, + clipboard when Allow Insecure is on).
--    Import: data\db\0x_import.json or a pasted snapshot (size-limited, every value validated).
--
--  FIXED IN 4.2
--    · error counters were shared by every handler of one event: a healthy player_hurt handler
--      reset the count of a failing one, so the failing one was never suspended
--    · the LC flag only expired on fresh net updates: dormant / frozen targets stayed "LC"
--    · a "reveal" stamp from before a clock reset froze a record until the map changed
--    · button actions could read a value from before the last menu edit (50 / 400 ms poll)
--    · "Shuffle when hit" kept shuffling after it was switched off; anti-aim state survived
--      level_shutdown
--    · two widgets named "Apex hitchance" in one group (same menu id)
--    · snapshot paths were not length / charset checked, pasted snapshots had no size limit,
--      snapshots of a newer schema were applied, the learned-side db was loaded unvalidated
--
--  m_angEyeAngles override requires "Allow Insecure". Without it the resolver runs in
--  tracking mode (overlay, stats, learning and the rage assist keep working).
-- ============================================================================

local META = {
    name           = "0x",
    version        = "4.2",
    schema         = 5,
    db             = "0x_resolver_v21",     -- learned sides (compatible with v2.1+)
    db_settings    = "0x_v4_settings",      -- menu snapshot (ids unchanged since v4.0)
    db_settings_v3 = "0x_s2_v3_settings",   -- v3.0 snapshot, imported once
    db_legacy      = "0x_v31_settings",     -- s1 snapshot, imported once
    db_journal     = "0x_v31_journal",      -- ragebot originals (crash-safe, compatible with v3.x)
    db_import      = "0x_import",           -- data\db\0x_import.json
    db_export      = "0x_export",           -- data\db\0x_export.json
    db_tetris      = "0x_tetris",           -- Tetris records
    credits        = "@kukluxk · @likvidatorchaes (subcult)",
    import_max     = 65536,                 -- bytes; larger pasted snapshots are rejected
}

-- Manual config paths when auto-discovery picks the wrong ones. Example: hc = { "ragebot.hitchance" }
-- Paths imported from a snapshot (web companion) are merged with these.
local CUSTOM_PATHS = { hc = {}, dmg = {}, safe = {}, baim = {}, hitbox = {} }
-- If safepoint in your ragebot is a dropdown, this is the index of the "Force" item.
local SAFE_COMBO_VALUE = 2

-- ----------------------------------------------------------------------------
-- Fast paths
-- ----------------------------------------------------------------------------
local floor, abs, sqrt, atan2, sin, cos, rad, deg = math.floor, math.abs, math.sqrt, math.atan2, math.sin, math.cos, math.rad, math.deg
local max, min = math.max, math.min
local pcall, pairs, type, tostring, tonumber, next = pcall, pairs, type, tostring, tonumber, next
local format, s_lower, s_find, s_gsub, s_sub, s_upper = string.format, string.lower, string.find, string.gsub, string.sub, string.upper
local tremove, tconcat, tsort = table.remove, table.concat, table.sort
local band = bit.band

local function normalize(a)
    a = a % 360
    if a > 180 then a = a - 360 end
    return a
end
local function clamp(v, lo, hi) if v < lo then return lo elseif v > hi then return hi end return v end
local function lerp(a, b, t) return a + (b - a) * t end
local function round(v) return floor(v + 0.5) end
local function sign(v) if v > 0 then return 1 elseif v < 0 then return -1 end return 0 end

-- Calls fn and swallows errors. Returns only the first result.
local function safe(fn, ...)
    if fn == nil then return nil end
    local ok, r = pcall(fn, ...)
    if ok then return r end
    return nil
end

-- Utility namespace (kept in one table to stay far below LuaJIT's 200-locals limit).
local U = {}

function U.copy(v)
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

-- Shallow structural equality (config values: numbers, booleans, strings, flat tables).
function U.same(a, b)
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

function U.any_match(s, list)
    for i = 1, #list do
        if s_find(s, list[i]) then return true end
    end
    return false
end

function U.utf8_len(s) return select(2, s_gsub(s, "[^\128-\193]", "")) end

function U.trim(s) return (s_gsub(s, "^%s+", ""):gsub("%s+$", "")) end

-- Angular distance of a direction (from -> to) to view angles va.
function U.fov(from, to, va)
    local dx, dy, dz = to.x - from.x, to.y - from.y, to.z - from.z
    local pitch = deg(atan2(-dz, sqrt(dx * dx + dy * dy)))
    local yaw = deg(atan2(dy, dx))
    local dp, dw = normalize(pitch - va.x), normalize(yaw - va.y)
    return sqrt(dp * dp + dw * dw)
end

-- Yaw of the direction from -> to (degrees).
function U.yaw_to(from, to) return deg(atan2(to.y - from.y, to.x - from.x)) end

local function say(msg) print("[0x] " .. tostring(msg)) end

-- ----------------------------------------------------------------------------
-- Constants
-- ----------------------------------------------------------------------------
local C = {                    -- resolver
    HISTORY          = 24,     -- yaw samples kept per player (~375 ms @ 64 tick; fits delayed jitter)
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
    BODY_EVERY       = 2,      -- fresh updates between hitbox reads per player
    FS_OFFSET        = 26,     -- u; lateral offset for freestanding traces
    FS_EVERY         = 4,      -- fresh updates between freestanding traces per player
    FACE_ANGLE       = 35,     -- deg; eye yaw this close to "at target" = probably aiming, not AA
    FACE_SCALE       = 0.3,    -- desync multiplier while facing us
    SPIN_LEAD        = 0.5,    -- updates of spin extrapolation (Jitter / Spin mode)
    REVEAL_TIME      = 0.04,   -- s; skip samples right after the enemy fired (yaw snaps to his aim)
    SHOT_DEDUPE      = 0.10,   -- s; min interval between pending shots on the same target
    LC_DIST_SQR      = 4096,   -- u^2; origin jump above 64 u between updates = LC break
    LC_HOLD          = 1.0,    -- s; LC flag stays this long after the last break
    SPREAD_BLAME     = 5.0,    -- u; spread cone radius at target distance above this blames spread
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
    SOFT_CONF_LOSS   = 0.05,   -- conf loss for misses not blamed on the resolver
    ROUND_CONF_DECAY = 0.85,
    JIT_PRED_CONF    = 0.6,    -- min share of regular runs to trust the jitter phase prediction
    JIT_MAX_PERIOD   = 8,      -- updates; longer holds are not treated as periodic jitter
    LC_FREEZE        = 0.2,    -- s; history is frozen this long after an LC break (Hold on LC break)
    MODE_CONFIRM     = 2,      -- consecutive classifications before the AA class switches
    HW_MIN = 0.4, HW_MAX = 1.6, HW_GAIN = 0.04, HW_LOSS = 0.06,   -- hint reliability bounds / steps
    FEED_LIFE        = 5.0,    -- s; event feed line lifetime
    FEED_MAX         = 6,
}

local K = {                    -- ragebot assist / runtime
    EVAL_TICKS   = 4,          -- target / lethality re-evaluation period, ticks
    VERIFY_TICKS = 16,         -- config cross-check period, ticks
    WEAPON_TICKS = 64,         -- weapon class re-check period, ticks
    HK_INTERVAL  = 1.0,        -- housekeeping period, s
    SAVE_DELAY   = 1.5,        -- autosave delay after the last menu change, s
    JOURNAL_LAZY = 15,         -- s of silence before stale journal entries are dropped from disk
    IO_RETRY     = 5,          -- pause after a failed disk write, s
    CM_TIMEOUT   = 0.5,        -- createmove silent longer than this -> ragebot values restored, s
    PAINT_TIMEOUT = 2,         -- paint silent longer than this -> createmove runs background tasks, s
    MAX_CANDS    = 48,         -- path candidates per parameter
    MAX_TARGETS  = 3,          -- closest-to-crosshair targets to trace
    HOLD_TICKS   = 12,         -- body-aim decision hold (anti flicker)
    MOVE_EPS     = 5,          -- "moving" threshold, u/s
    T_MOVE_SQR   = 1600,       -- target "running" above 40 u/s (squared)
    BAD_LIMIT    = 3,          -- consecutive write failures before a path is disabled
    MISM_LIMIT   = 3,          -- consecutive foreign overwrites before a path is disabled
    ERR_LIMIT    = 25,         -- consecutive callback errors before suspension
    ERR_COOLDOWN = 5,          -- suspension length, s
    ERR_STRIKES  = 3,          -- suspensions before a full stop
    ERR_FORGIVE  = 60,         -- s without errors after which strikes are forgotten
    EYE_OFFSET   = 46,         -- aim point height above the target origin
    HB_TTL       = 256,        -- hitbox id cache lifetime, ticks
    HB_MAX       = 64,
    GRAVITY      = 800,
    SIM_MARGIN   = 16,
    MEMO_MAX     = 512,
    HG_HEAD = 1, HG_CHEST = 2, HG_STOMACH = 3,
    FL_DUCKING   = 2,
    BTN_SPEED    = (buttons and buttons.speed) or 65536,
    BTN_ATTACK   = (buttons and buttons.attack) or 1,
    BTN_ATTACK2  = (buttons and buttons.attack2) or 2048,
    BTN_USE      = (buttons and buttons.use) or 32,
    MT_NOCLIP = 7, MT_LADDER = 9,   -- MoveType_t values reported by engine.post_state().move_type
    DEF_REVOLVER = 64,
    AA_SCAN_TICKS = 4,              -- at-target / anti-backstab / freestanding refresh period
    AA_FS_OFFSET  = 28,             -- u; lateral offset of the freestanding traces
    AA_FAIL_LIMIT = 20,             -- consecutive rejected angle writes before the anti-aim stops
    VK_LBUTTON   = 1,
}

local BRUTE = { 1.0, -1.0, 0.5, -0.5, 0.0, 0.75, -0.75 }   -- x max desync; index 1 is the trusted guess
local STEP_SEQ = { 0, 1, -1, 2, -2 }                        -- x brute step
-- Jitter model candidates (x half range, toward the predicted side): index 1 is the trusted guess.
local JIT_SEQ = { [1] = { 0, 1, -1, 0.5, -0.5 }, [2] = { 1, -1, 0, 0.5, -0.5 } }

-- Enumerations (one table: fewer main-chunk locals, no accidental globals).
local E = {
    MODE_ADAPTIVE = 1, MODE_STATIC = 2, MODE_BRUTE = 3, MODE_JITSPIN = 4, MODE_OFFSET = 5,
    JIT_CENTER = 1, JIT_PREDICT = 2, JIT_FOLLOW = 3,
    BASE_AUTO = 1, BASE_EYE = 2, BASE_TARGET = 3,
    PITCH_OFF = 1, PITCH_CLAMP = 2, PITCH_AUTO = 3, PITCH_DOWN = 4, PITCH_ZERO = 5, PITCH_UP = 6,
    PAT_MULT = 1, PAT_STEP = 2,
    STAGE_LAGCOMP = (stage and stage.lagcomp) or 6,
    STAGE_NET_END = (stage and stage.net_update_end) or 7,
    MASK_VISIBLE  = (trace and trace.mask and trace.mask.visible) or 1847299,
}
local EYE_CLASSES = { "C_CSPlayerPawn", "C_CSPlayerPawnBase", "CCSPlayerPawn" }
local MODE_LABEL  = { static = "STATIC", sway = "SWAY", jitter = "JITTER", spin = "SPIN", random = "RANDOM" }

local ST = { STAND = 1, SLOW = 2, MOVE = 3, DUCK = 4, AIR = 5, APEX = 6 }
local ST_NAME = { "STAND", "WALK", "RUN", "DUCK", "AIR", "APEX" }

local WPN = {
    ITEMS = { "SSG 08", "AWP", "Auto snipers", "Deagle / R8", "Pistols", "Other" },
    BY_DEF = {
        [40] = 1, [9] = 2, [11] = 3, [38] = 3, [1] = 4, [64] = 4,
        [2] = 5, [3] = 5, [4] = 5, [30] = 5, [32] = 5, [36] = 5, [61] = 5, [63] = 5,
    },
    BY_NAME = {
        { "ssg08", 1 }, { "awp", 2 }, { "g3sg1", 3 }, { "scar20", 3 }, { "deagle", 4 }, { "revolver", 4 },
        { "elite", 5 }, { "fiveseven", 5 }, { "glock", 5 }, { "tec9", 5 }, { "hkp2000", 5 },
        { "p250", 5 }, { "usp", 5 }, { "cz75", 5 },
    },
    NON_GUN = {
        "knife", "bayonet", "grenade", "flashbang", "smoke", "molotov", "incgrenade", "decoy", "c4",
        "taser", "healthshot", "fists", "melee", "axe", "hammer", "spanner", "tablet", "shield",
        "breach", "bump", "inferno",
    },
    NON_GUN_DEF = { [31] = true, [41] = true, [42] = true, [57] = true, [59] = true, [69] = true,
                    [70] = true, [72] = true, [74] = true, [75] = true, [76] = true, [78] = true, [85] = true },
}
for d = 43, 49 do WPN.NON_GUN_DEF[d] = true end
for d = 500, 526 do WPN.NON_GUN_DEF[d] = true end

function WPN.non_gun_name(name)
    if type(name) ~= "string" or name == "" then return false end
    local l = s_lower(name)
    for i = 1, #WPN.NON_GUN do
        if s_find(l, WPN.NON_GUN[i], 1, true) then return true end
    end
    return false
end

-- ----------------------------------------------------------------------------
-- Shared runtime state
-- ----------------------------------------------------------------------------
local STATE = {
    rt = 0,                                -- realtime snapshot for the current callback
    insecure = false,
    menu_open = false, menu_evt_t = -1e9, menu_poll_t = -1e9,
    cmd_angles = nil,                      -- angles actually sent (silent aim aware)
    lp_air = false, lp_moving = false,     -- local movement, refreshed every createmove
    sw = 0, sh = 0,
    failed = false, suspend_until = nil, strikes = 0, strike_t = 0, errs = {},
    rep_last = nil, rep_t = -100,
    last_label = 0,
    flip_prev = false,
    kb_captured = false,                   -- Tetris owns the keyboard: bind edges are frozen
    prof = {},                             -- smoothed callback cost in ms (debug panel)
}

-- Module tables. Keeping functions in tables keeps every closure far below the 60-upvalue
-- limit of LuaJIT and the main chunk far below 200 locals.
local RES, RB, VIS, ACT, Bind, Journal, IO, ESPX, AA, TET = {}, {}, {}, {}, {}, {}, {}, {}, {}, {}

local function report(where, err)
    local msg = tostring(err)
    if msg ~= STATE.rep_last or STATE.rt - STATE.rep_t > 5 then
        STATE.rep_last, STATE.rep_t = msg, STATE.rt
        say("error in " .. where .. ": " .. msg)
    end
end

-- ============================================================================
--  MENU: registry, fault-tolerant constructors, snapshot
-- ============================================================================
local UI, REG, ORDER, CFG = {}, {}, {}, {}
local MENU = { combo_base = nil, last = -1e9, built = false }
local SET = { dirty = false, dirty_t = 0, io_t = -1e9 }
local PS = { last = nil, sync = true, applying = false }
local PATHS_USER = { hc = {}, dmg = {}, safe = {}, baim = {}, hitbox = {} }   -- from snapshots

-- A failed element must not take the script down: it is replaced by an inert stand-in.
-- Stand-ins are tracked in a side table: API objects are never probed for unknown fields.
local DUMMY = setmetatable({}, { __mode = "k" })
local function is_dummy(el) return el == nil or DUMMY[el] == true end

local function dummy_el(def)
    local d = {}
    DUMMY[d] = true
    d.get = function() return def end
    d.set = function() end
    d.depends = function() return d end
    d.tooltip = function() return d end
    d.callback = function() return d end
    d.visible = function() return false end
    d.active = function() return false end
    return d
end

local function create(g, ctor, id, def, ...)
    if type(ctor) ~= "function" then
        return dummy_el(def)
    end
    local ok, el = pcall(ctor, g, ...)
    if not ok or el == nil then
        say("menu element '" .. tostring(id) .. "' not created: " .. tostring(el))
        el = dummy_el(def)
    end
    return el
end

local function reg(id, kind, el, def, lo, hi, items, tip)
    REG[id] = { id = id, kind = kind, el = el, def = def, lo = lo, hi = hi, items = items }
    ORDER[#ORDER + 1] = id
    UI[id] = el
    if tip and not is_dummy(el) then pcall(el.tooltip, el, tip) end
    return el
end

-- Combo items are 1-based everywhere in this script; the widget base (0 or 1) is detected once.
local function set_combo(el, items, idx1)
    if is_dummy(el) then return end
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

local W = {}   -- widget constructors

function W.chk(g, id, name, def, tip)
    return reg(id, "check", create(g, g.checkbox, id, def, name, def), def, nil, nil, nil, tip)
end

function W.sld(g, id, name, lo, hi, def, fmt, tip)
    return reg(id, "slider", create(g, g.slider_int, id, def, name, lo, hi, def, fmt or "%d"), def, lo, hi, nil, tip)
end

function W.cmb(g, id, name, items, def1, tip)
    local el = create(g, g.combo, id, def1, name, items)
    if not is_dummy(el) then
        local v = safe(el.get, el)
        if MENU.combo_base == nil and type(v) == "number" then
            MENU.combo_base = (v == 0) and 0 or 1
        end
        if def1 > 1 then set_combo(el, items, def1) end
    end
    return reg(id, "combo", el, def1, 1, #items, items, tip)
end

function W.clr(g, id, name, def, tip)
    return reg(id, "color", create(g, g.color, id, def, name, def, true), def, nil, nil, nil, tip)
end

function W.key(g, id, name, tip)
    return reg(id, "key", create(g, g.keybind, id, false, name, 0), false, nil, nil, nil, tip)
end

function W.mcb(g, id, name, items, defs, tip)
    return reg(id, "multi", create(g, g.multi_combo, id, defs, name, items, defs), defs, nil, nil, items, tip)
end

function W.lbl(g, text)
    return create(g, g.label, "label", nil, text)
end

function W.btn(g, id, name, act, tip)
    local el = create(g, g.button, id, nil, name, function()
        local f = ACT[act]
        if not f then return end
        STATE.rt = globals.realtime()
        pcall(ACT.sync)                          -- a value changed a moment ago must be visible to the action
        local ok, err = pcall(f)
        if not ok then report("button " .. act, err) end
    end)
    if tip and not is_dummy(el) then pcall(el.tooltip, el, tip) end
    return el
end

function W.div(g, text) if type(g.divider) == "function" then pcall(g.divider, g, text) end end

function W.dep(el, other)
    if is_dummy(el) or is_dummy(other) then return el end
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
    if el == nil or is_dummy(el) then return false end
    local ok, v = pcall(el.active, el)
    return ok and v == true
end

local ITEMS = {
    MODE    = { "Adaptive", "Static side", "Bruteforce", "Jitter / Spin", "Static offset" },
    JIT     = { "Center", "Predict next", "Follow last" },
    BASE    = { "Auto", "Eye yaw", "At target" },
    PITCH   = { "Off", "Clamp", "Auto", "Force down", "Force zero", "Force up" },
    BRUTE   = { "Multipliers", "Stepped" },
    OVERLAY = { "Compact", "Detailed" },
    PRESET  = { "Custom", "Balanced", "Aggressive", "Conservative" },
    AIR     = { "Ground + vertical speed", "Ground flag only", "Landing prediction" },
    -- Indices 1..6 of AA_STATE, 1..5 of AA_PITCH and 1..8 of AA_MOD are identical to v4.1 (snapshot compatible).
    AA_STATE  = { "Shared", "Standing", "Walking", "Running", "Ducking", "Air", "Duck-moving", "Air-duck" },
    AA_PITCH  = { "Off", "Down", "Up", "Zero", "Custom", "Jitter (down / up)", "Sway", "Random" },
    AA_BASE   = { "Local view", "At target" },
    AA_MOD    = { "Off", "Center jitter", "Offset jitter", "3-way", "5-way", "Spin", "Sway", "Random", "Skitter", "Flick" },
    AA_FIX    = { "Engine (rotate_movement)", "Manual (set_move)", "Off" },
    AA_TGT    = { "Closest to crosshair", "Nearest" },
    AA_AB     = { "Off", "Shift phase", "Flip offset", "Step variants" },
    AA_SAFE   = { "Knife out", "Height advantage" },
    AA_PRESET = { "Jitter backward", "Static backward", "Spin", "Delayed wide jitter", "5-way", "Low sway",
                  "Skitter random", "Per-state meta", "Chaos", "Low profile" },
    HS_NEED   = { "Head shot is lethal", "Head beats body", "Whenever trusted" },
    HS_STATES = { "Standing", "Ducking", "Walking", "Running" },
    TET_VIEW  = { "Floating window", "Inside this tab" },
    TET_KEYS  = { "Arrows + Z / X / C", "WASD + J / K / L" },
}

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
    if type(tab.group) ~= "function" then return {} end
    local ok, g = pcall(tab.group, tab, name)
    if not ok or not g then
        say("group '" .. name .. "' not created: " .. tostring(g))
        return {}
    end
    return g
end

-- ---------------------------------------------------------------- menu layout (v4.2)
-- Six tabs, one job each. Every tab starts with its master switch; everything below it
-- depends on that switch. Element ids are unchanged since v4.0, so old snapshots still load.
--   0x Resolver  General · Jitter & brute · Hints · Learning
--   0x Rage      Assist · Headshot assist · Body-aim · Accuracy · Air · Binds · Config link
--   0x Anti-Aim  General · Builder · Manual & freestanding · Reactions · Safety
--   0x Visuals   Players · Panel · Style
--   0x Tetris    Game · Options · Records
--   0x Config    Settings · Data · About
local BUILD = {}

function BUILD.resolver()
    local chk, sld, cmb, key, dep = W.chk, W.sld, W.cmb, W.key, W.dep
    local tab = mk_tab("0x Resolver")

    local g = mk_group(tab, "General")
    local enable = chk(g, "enable", "Enable resolver", true, "Master switch of the resolver. The rage assist has its own switch on the 0x Rage tab.")
    dep(chk(g, "apply", "Override eye angles", true, "Writes the resolved angles into m_angEyeAngles every net update.\nRequires Allow Insecure; without it the resolver only tracks."), enable)
    dep(cmb(g, "mode", "Mode", ITEMS.MODE, E.MODE_ADAPTIVE,
        "Adaptive: all hints + learning + brute cycling.\nStatic side: learned side only.\nBruteforce: cycle the pattern on misses.\nJitter / Spin: jitter -> center, spin -> extrapolated yaw.\nStatic offset: yaw relative to you (Yaw offset)."), enable)
    dep(sld(g, "desync", "Max desync", 0, 90, 58, "%d°", "Desync amount applied to the base yaw."), enable)
    dep(sld(g, "yaw_off", "Yaw offset", -180, 180, 0, "%d°", "Static offset mode: resolved yaw = (yaw towards you) + offset."), enable)
    dep(cmb(g, "base", "Yaw base", ITEMS.BASE, E.BASE_AUTO, "Auto: spin -> at target, jitter -> center, otherwise eye yaw."), enable)
    dep(cmb(g, "pitch", "Pitch", ITEMS.PITCH, E.PITCH_AUTO, "Auto resolves fake pitch flicker to down and clamps the rest."), enable)
    dep(sld(g, "move_sc", "Moving correction", 0, 100, 35, "%d%%", "Share of the desync applied while the enemy moves."), enable)
    dep(chk(g, "face_damp", "Facing-target damping", true, "An eye yaw within 35° of you usually means he is aiming, not anti-aiming: desync is scaled down."), enable)
    key(g, "k_flip", "Flip target side", "Press: inverts the learned side of the crosshair target.")

    local gj = mk_group(tab, "Jitter & brute")
    dep(cmb(gj, "jit_mode", "Jitter handling", ITEMS.JIT, E.JIT_CENTER,
        "Center: aim at the middle of both jitter angles; a resolver miss steps to the predicted angle, then to the other one.\nPredict next: start at the angle the NEXT update is expected to have (both clusters and the switch period are learned; irregular patterns fall back to Center).\nFollow last: use the last received yaw."), enable)
    dep(sld(gj, "jit_sc", "Jitter correction", 0, 100, 50, "%d%%", "Share of the desync applied on top of the jitter center."), enable)
    dep(cmb(gj, "brute_pat", "Brute pattern", ITEMS.BRUTE, E.PAT_MULT, "Multipliers: 1, -1, 0.5, -0.5, 0, 0.75, -0.75 x max desync.\nStepped: 0, +1, -1, +2, -2 x brute step."), enable)
    dep(sld(gj, "brute_step", "Brute step", 5, 90, 30, "%d°", "Step of the Stepped pattern."), enable)
    dep(chk(gj, "brute_skip", "Skip offsets that just missed", true, "4.2: an effective offset (side x multiplier) that produced a resolver miss is not tried again for 20 s,\neven after the side flipped. When everything failed the list restarts at the entry that hit last."), enable)

    local gi = mk_group(tab, "Hints")
    dep(chk(gi, "body", "Body yaw hint", true, "Estimates lower/upper body yaw from hitbox geometry."), enable)
    dep(chk(gi, "freestand", "Freestanding hint", true, "Traces cover left/right of the head; freestanding AA hides toward cover."), enable)
    dep(chk(gi, "move_mem", "Movement memory", true, "Remembers the last movement yaw for a second after the enemy stops."), enable)
    dep(chk(gi, "move_dir", "Side from movement direction", true, "While running, the side is hinted by the movement direction relative to you."), enable)
    dep(chk(gi, "lc_detect", "Lag-compensation watch", true, "Teleports and simulation-time rewinds flag the target as LC-broken:\nmisses on it do not step the brute table and the rage assist treats it as unresolved."), enable)
    dep(chk(gi, "lc_hold", "Hold on LC break", true, "For 0.2 s after a lag-compensation break the yaw history is frozen and the last stable angles stay applied."), enable)

    local gl = mk_group(tab, "Learning")
    local feedback = dep(chk(gl, "feedback", "Hit / miss learning", true, "weapon_fire + player_hurt feedback drives side confidence and brute cycling."), enable)
    dep(sld(gl, "miss_win", "Miss window", 150, 1000, 350, "%d ms", "A shot without player_hurt within this window counts as a miss."), feedback)
    dep(sld(gl, "miss_tol", "Misses before step", 1, 3, 1, nil, "Consecutive resolver misses on a standing target before the brute index steps."), feedback)
    dep(chk(gl, "spread_blame", "Ignore spread misses", true, "A miss with a spread cone wider than the head at that distance is blamed on spread, not on the resolver."), feedback)
    dep(chk(gl, "body_partial", "Body hit = partial", true, "A body hit while body-aim was not forced gives reduced confidence and does not lock the brute index."), feedback)
    dep(chk(gl, "anti_ab", "Detect anti-bruteforce", true, "If the target flips his side after every hit, the next prediction flips with him."), feedback)
    dep(chk(gl, "cls_mem", "Side memory per AA class", true, "4.2: the confirmed side is remembered separately for static / sway / jitter / spin / random,\nso a target that switches anti-aim does not inherit the wrong side."), feedback)
    dep(chk(gl, "hint_learn", "Hint reliability learning", true, "Confirmed hits and resolver misses re-weight the body / freestanding / movement hints for this session."), feedback)
    dep(chk(gl, "flip_on_hurt", "Flip side when they hit you", false, "Invert the learned side of an enemy who just hit you."), feedback)
    dep(chk(gl, "persist", "Persist learning (db)", true, "Keeps learned sides per SteamID between sessions."), feedback)
end

function BUILD.rage()
    local chk, sld, cmb, key, mcb, btn, div, dep = W.chk, W.sld, W.cmb, W.key, W.mcb, W.btn, W.div, W.dep
    local tab = mk_tab("0x Rage")

    local gm = mk_group(tab, "Assist")
    local rb = chk(gm, "rb_enable", "Enable rage assist", true, "Drives hitchance, min damage, safepoint and hitboxes of your ragebot through config paths.\nEverything is restored on pause, death, weapon change and unload.")
    dep(cmb(gm, "preset", "Preset", ITEMS.PRESET, 2, "Balanced is universal, Aggressive fires sooner, Conservative wants more certainty.\nEditing a value switches the preset to Custom."), rb)
    dep(mcb(gm, "weapons", "Weapon groups", WPN.ITEMS, { true, true, true, true, true, false }, "The assist only touches the ragebot while one of the selected groups is active."), rb)
    dep(chk(gm, "pause_menu", "Pause while menu is open", true, "Your values are restored while the menu is open so you can edit the ragebot freely."), rb)

    local gh = mk_group(tab, "Headshot assist")
    local hs = dep(chk(gh, "hs_on", "Headshot assist", true, "4.2: when the resolver trusts its guess and the head is the better target, the ragebot is narrowed to the head:\nhitboxes become head-only, hitchance gets a bonus and (optionally) min damage is lifted above the body damage.\nNeeds the resolver. Never active on airborne / LC-breaking / unresolved targets."), rb)
    dep(sld(gh, "hs_trust", "Minimum resolver trust", 30, 95, 62, "%d%%", "Trust mixes side confidence, AA class, jitter prediction quality, hit / miss streaks and the brute index."), hs)
    dep(cmb(gh, "hs_need", "Go for the head when", ITEMS.HS_NEED, 2, "Head shot is lethal: only a killing head shot.\nHead beats body: lethal, or at least 25% more damage than the best body hitbox.\nWhenever trusted: trust alone decides."), hs)
    dep(mcb(gh, "hs_states", "Target states", ITEMS.HS_STATES, { true, true, true, false }, "The head is only forced while the target is in one of these states."), hs)
    dep(chk(gh, "hs_body_first", "Lethal body shot wins", true, "If one body shot kills, the body stays the target (safer than any head shot)."), hs)
    dep(sld(gh, "hs_hc", "Head hitchance bonus", 0, 25, 6, "+%d%%", "Added to the hitchance while the head is forced."), hs)
    dep(chk(gh, "hs_gate", "Damage gate", true, "Min damage is set just above the best body damage, so only a head shot satisfies it.\nUseful when no hitbox path was found. Never above the target's HP."), hs)
    key(gh, "k_head", "Force head", "While held: head-only hitboxes regardless of trust.")

    local gba = mk_group(tab, "Body-aim")
    local baim = dep(chk(gba, "baim_on", "Smart body-aim", true, "Body damage is traced; the head is removed from the hitboxes when the body is the better target."), rb)
    dep(chk(gba, "baim_lethal", "Body kills in 1 shot", true), baim)
    dep(chk(gba, "baim_2x", "Body kills in 2 shots", false, "Two body hits kill while one head hit would not (Deagle, pistols)."), baim)
    dep(sld(gba, "baim_margin", "Damage margin", 0, 30, 2, "%d HP"), baim)
    dep(chk(gba, "baim_hp_on", "Body at low HP", false), baim)
    dep(sld(gba, "baim_hp", "HP threshold", 1, 100, 40, "%d HP"), baim)
    dep(chk(gba, "baim_unres", "Body when unresolved", true, "Low-trust random / wide jitter targets, repeated misses, a deep brute index or an LC break get body-aim (reason RES / LC)."), baim)

    local gc = mk_group(tab, "Accuracy")
    local hc_on = dep(chk(gc, "hc_on", "Hitchance by state", true, "Own hitchance for standing, walking, running and ducking. 0 keeps yours."), rb)
    dep(sld(gc, "hc_stand", "Standing", 0, 100, 70, "%d%%"), hc_on)
    dep(sld(gc, "hc_slow", "Walking", 0, 100, 65, "%d%%"), hc_on)
    dep(sld(gc, "hc_move", "Running", 0, 100, 55, "%d%%"), hc_on)
    dep(sld(gc, "hc_duck", "Ducking", 0, 100, 72, "%d%%"), hc_on)
    div(gc, "Target")
    dep(sld(gc, "baim_fov", "Target search FOV", 5, 180, 60, "%d°", "Angle around the crosshair in which the target for corrections, damage cap, head and body decisions is searched."), rb)
    dep(sld(gc, "hc_tgt_air", "Target in air", -30, 30, -8, "%+d%%"), rb)
    dep(sld(gc, "hc_tgt_move", "Target running", -30, 30, 0, "%+d%%"), rb)
    dep(sld(gc, "unres_hc", "Target unresolved", -30, 30, 8, "%+d%%", "Hitchance adjustment when the resolver has little trust in its guess or the target breaks lag compensation."), rb)
    dep(chk(gc, "dmg_cap", "Cap min damage at target HP", true, "A finishing shot is never blocked by a min damage above the target's HP."), rb)

    local ga = mk_group(tab, "Air")
    local air = dep(chk(ga, "air_on", "Jump optimizer", true, "Air hitchance, min damage and safepoint while you are airborne.\nSSG 08 reference: hitchance 65-78, damage 45-65."), rb)
    dep(sld(ga, "air_hc", "Air hitchance", 1, 100, 70, "%d%%"), air)
    dep(sld(ga, "air_dmg", "Air min damage", 1, 130, 50, "%d HP"), air)
    dep(chk(ga, "air_safe", "Air safepoint", true), air)
    local apex = dep(chk(ga, "apex_on", "Apex hitchance", true, "At the top of the jump the vertical speed is near zero and spread is minimal."), air)
    dep(sld(ga, "apex_hc", "Hitchance at apex", 1, 100, 58, "%d%%"), apex)
    dep(sld(ga, "apex_win", "Apex window", 10, 110, 42, "≤ %d u/s", "Apex while |vertical speed| is below this."), apex)
    div(ga, "Detection")
    dep(cmb(ga, "air_mode", "Air detection", ITEMS.AIR, 1, "Ground + vertical speed ignores stairs. Ground flag only reacts fastest.\nLanding prediction restores ground values a few ticks before touchdown (engine.simulate)."), rb)
    dep(sld(ga, "air_thr", "Vertical speed threshold", 5, 220, 22, "%d u/s"), rb)
    dep(sld(ga, "land_ticks", "Landing lead", 1, 8, 3, "%d ticks"), rb)

    local gb = mk_group(tab, "Binds")
    key(gb, "k_strict", "Strict · max accuracy", "While held: hitchance + Strict bonus, safepoint forced.")
    dep(sld(gb, "strict_bonus", "Strict hitchance bonus", 0, 40, 12, "+%d%%"), rb)
    key(gb, "k_baim", "Force body-aim", "While held: head is removed from the hitboxes. Wins over Force head.")
    key(gb, "k_dmg", "Min damage override", "While held: min damage = the value below.")
    dep(sld(gb, "dmg_bind_val", "Override min damage", 1, 130, 30, "%d HP"), rb)

    local gl = mk_group(tab, "Config link")
    UI.rb_status = W.lbl(gl, "Paths: scanning…")
    btn(gl, "rescan", "Rescan config", "rescan", "Find the ragebot paths in config.keys again.")
    btn(gl, "dump", "Dump paths to console", "dump", "Prints the discovered paths with their current values.")
    dep(chk(gl, "log_cfg", "Log config writes", false, "Prints path, old and new value of every config write to the Lua console."), rb)
end

function BUILD.antiaim()
    local chk, sld, cmb, key, mcb, btn, dep = W.chk, W.sld, W.cmb, W.key, W.mcb, W.btn, W.dep
    local tab = mk_tab("0x Anti-Aim")

    local g = mk_group(tab, "General")
    local aa = chk(g, "aa_on", "Enable anti-aim", false, "Writes pitch / yaw into the command in createmove (cmd:set_view_angles).\nNever active while you attack, hold a grenade / C4, use, or climb a ladder.")
    cmb(g, "aa_preset", "Preset", ITEMS.AA_PRESET, 1, "A preset rewrites every condition of the builder (and a few reactions). Pick one, press Apply, then tune it.")
    btn(g, "aa_apply", "Apply preset", "aa_preset_apply", "Overwrites the builder with the selected preset.")
    dep(cmb(g, "aa_target", "At-target picks", ITEMS.AA_TGT, 1, "Which enemy the At target yaw base and freestanding follow."), aa)
    dep(cmb(g, "aa_fix", "Movement fix", ITEMS.AA_FIX, 1, "Keeps WASD relative to your camera while the command yaw is turned.\nEngine: cmd:rotate_movement(camera yaw). Manual: the move vector is rotated in the script (cmd:set_move).\nIf you walk in the wrong direction, switch the mode."), aa)
    dep(chk(g, "aa_fix_inv", "Manual fix: invert side axis", false, "Only for the Manual fix: enable if strafing is mirrored."), aa)
    dep(chk(g, "aa_lock", "Lock angles", false, "Calls cmd:lock_angles() after the angles are written."), aa)

    local gb = mk_group(tab, "Builder")
    cmb(gb, "aa_edit", "Edit condition", ITEMS.AA_STATE, 1, "Shared is used by every condition without its own override.\nDuck-moving falls back to Ducking, Air-duck to Air, then to Shared.")
    btn(gb, "aa_copy", "Copy Shared into this condition", "aa_copy_shared", "Starts the selected condition from the Shared values and enables its override.")
    btn(gb, "aa_clear", "Reset this condition", "aa_reset_cond", "Back to defaults (override off).")
    for i = 1, #ITEMS.AA_STATE do
        local tag, p = ITEMS.AA_STATE[i] .. " · ", "aa" .. i .. "_"
        if i > 1 then chk(gb, p .. "on", tag .. "override", false, "Use these values instead of the fallback while " .. s_lower(ITEMS.AA_STATE[i]) .. ".") end
        cmb(gb, p .. "pitch", tag .. "pitch", ITEMS.AA_PITCH, 2, "Jitter alternates down / up with the yaw phase, Sway oscillates inside ± custom pitch, Random picks a new pitch each phase.")
        sld(gb, p .. "pitch_v", tag .. "custom pitch", -89, 89, 89, "%d°", "Used by Custom and Sway.")
        cmb(gb, p .. "base", tag .. "yaw base", ITEMS.AA_BASE, 2, "At target falls back to the local view while no enemy is known.")
        sld(gb, p .. "yaw", tag .. "yaw offset", -180, 180, 180, "%d°", "180 = backward.")
        sld(gb, p .. "yaw_l", tag .. "left add", -60, 60, 0, "%d°", "Extra yaw while the modifier is on its left (+) side. Makes jitter asymmetric.")
        sld(gb, p .. "yaw_r", tag .. "right add", -60, 60, 0, "%d°", "Extra yaw while the modifier is on its right (-) side.")
        cmb(gb, p .. "mod", tag .. "yaw modifier", ITEMS.AA_MOD, 1, "Center jitter: ± range / 2. Offset jitter: 0 / + range. 3-way, 5-way and Skitter step across the range.\nSpin and Sway use the speed. Random picks a new offset inside the range.\nFlick: every <speed> ticks the yaw jumps by the range for <delay> ticks.")
        sld(gb, p .. "range", tag .. "modifier range", 0, 180, 60, "%d°")
        sld(gb, p .. "rnd", tag .. "range randomization", 0, 100, 0, "%d%%", "Each phase the range shrinks by a random share up to this value.")
        sld(gb, p .. "delay", tag .. "switch delay", 1, 16, 1, "%d ticks", "Ticks each jitter / way / random step is held.")
        sld(gb, p .. "delay_max", tag .. "switch delay max", 1, 16, 1, "%d ticks", "Above the delay: every step is held for a random number of ticks between both values.")
        sld(gb, p .. "speed", tag .. "speed / period", 1, 90, 20, "%d", "Spin, Sway: degrees per tick. Flick: period in ticks.")
    end

    local gk = mk_group(tab, "Manual & freestanding")
    key(gk, "k_aa_left", "Manual left", "Yaw = camera + 90°. The most recently activated manual bind wins.")
    key(gk, "k_aa_right", "Manual right", "Yaw = camera - 90°.")
    key(gk, "k_aa_back", "Manual back", "Yaw = camera + 180°.")
    key(gk, "k_aa_fwd", "Manual forward", "Yaw = camera.")
    dep(chk(gk, "aa_manual_static", "Manual yaw disables modifier", true), aa)
    key(gk, "k_aa_fs", "Freestanding", "While active the yaw turns toward the side that is covered from the target.")
    dep(chk(gk, "aa_fs_always", "Freestanding always on", false, "Freestanding without holding the bind."), aa)
    dep(chk(gk, "aa_fs_static", "Freestanding disables modifier", true), aa)
    dep(chk(gk, "aa_fs_noair", "No freestanding in air", true, "Cover changes too fast while airborne."), aa)
    dep(chk(gk, "aa_edge", "Edge yaw", false, "Standing or ducking next to a wall (within 30 u): the yaw turns toward the wall. Below manual, anti-backstab and freestanding."), aa)
    key(gk, "k_aa_off", "Disable while held", "Anti-aim is not applied while this bind is active.")

    local gr = mk_group(tab, "Reactions")
    local ab = dep(cmb(gr, "aa_ab", "Anti-bruteforce", ITEMS.AA_AB, 1, "An enemy shot aimed at you that did no damage counts as his miss; every miss changes your angle.\nShift phase: the modifier jumps one phase. Flip offset: an extra offset with alternating sign.\nStep variants: +1, -1, +2, -2 x offset."), aa)
    dep(sld(gr, "aa_ab_off", "Anti-brute offset", 0, 60, 18, "%d°"), ab)
    dep(sld(gr, "aa_ab_time", "Anti-brute memory", 1, 20, 6, "%d s", "Without new misses the variant resets after this time. Also reset every round."), ab)
    local hurt = dep(chk(gr, "aa_hurt", "Shuffle when hit", true, "Bullet damage taken: the phase shifts and the yaw gets an extra offset whose sign flips with every hit."), aa)
    dep(sld(gr, "aa_hurt_off", "Shuffle offset", 0, 45, 12, "%d°"), hurt)
    dep(sld(gr, "aa_hurt_time", "Shuffle duration", 1, 10, 4, "%d s"), hurt)
    local knife = dep(chk(gr, "aa_knife", "Anti-backstab", true, "An enemy with a knife inside the distance below: face him so your back is not exposed."), aa)
    dep(sld(gr, "aa_knife_dist", "Anti-backstab distance", 100, 400, 220, "%d u"), knife)
    dep(mcb(gr, "aa_safe", "Safe head", ITEMS.AA_SAFE, { false, false }, "Static backward at the target with pitch down (no modifier) while you hold a knife or stand clearly above the target."), aa)

    local gs = mk_group(tab, "Safety")
    dep(chk(gs, "aa_use", "Stand down on use (E)", true, "Defusing, doors and pickups need your real angles."), aa)
    dep(chk(gs, "aa_freeze", "Stand down in freeze time", true), aa)
    dep(chk(gs, "aa_warmup", "Stand down in warmup", false), aa)
    dep(chk(gs, "aa_ladder", "Stand down on ladder / noclip", true, "Read from engine.post_state().move_type."), aa)
end

function BUILD.visuals()
    local chk, sld, cmb, clr = W.chk, W.sld, W.cmb, W.clr
    local tab = mk_tab("0x Visuals")

    local g = mk_group(tab, "Players")
    chk(g, "overlay", "Player overlay", true, "AA class, side and desync above every tracked enemy.")
    cmb(g, "ov_style", "Overlay style", ITEMS.OVERLAY, 1, "Detailed adds confidence bar, hits / misses, brute index and pitch class.")
    chk(g, "yaw_lines", "Yaw lines", true, "Short lines from the head: dim = received yaw, accent = resolved yaw.")
    chk(g, "esp_flag", "Native ESP flag", false, "Adds the AA class / side as a flag to the built-in player ESP (esp.add_text).")

    local gp = mk_group(tab, "Panel")
    chk(gp, "panel", "Status panel", true, "Movement state, live ragebot overrides and the crosshair target's AA.\nDrag it with the mouse while the menu is open.")
    sld(gp, "panel_x", "Panel X", 0, 100, 1, "%d%%")
    sld(gp, "panel_y", "Panel Y", 0, 100, 40, "%d%%")
    sld(gp, "panel_scale", "Panel scale", 80, 150, 100, "%d%%")
    chk(gp, "feed", "Event feed", true, "Hit / miss / brute events under the panel.")
    chk(gp, "aa_arrows", "Anti-aim arrows", true, "Arrow next to the crosshair for a manual direction (accent) or freestanding / edge (amber).")

    local gs = mk_group(tab, "Style")
    clr(gs, "accent", "Accent color", color(140, 148, 255, 255), "Overlay, lines, panel and Tetris accent.")
    chk(gs, "log_hits", "Log shots to console", false, "Prints every hit / miss with its classified reason to the Lua console.")
    chk(gs, "debug", "Debug panel", false, "Per-record internals, module state and callback timings.")
end

function BUILD.tetris()
    local chk, sld, cmb, btn, lbl = W.chk, W.sld, W.cmb, W.btn, W.lbl
    local tab = mk_tab("0x Tetris")

    local g = mk_group(tab, "Game")
    chk(g, "tet_on", "Show Tetris", false, "Opens the game. It only reads the keyboard while it is visible and running;\nmanual anti-aim binds and the resolver flip bind are frozen meanwhile.")
    btn(g, "tet_new", "New game", "tet_new")
    btn(g, "tet_pause", "Pause / resume", "tet_pause")
    UI.tet_canvas = create(g, g.custom, "tet_canvas", nil, "Tetris", 372, function(x, y, w, h)
        TET.embed_draw(x, y, w, h)
    end)

    local go = mk_group(tab, "Options")
    cmb(go, "tet_view", "Display", ITEMS.TET_VIEW, 1, "Floating window: drawn on screen, drag it by the title while the menu is open.\nInside this tab: drawn in the Game group (falls back to the window if the menu cannot host it).")
    chk(go, "tet_ingame", "Playable with the menu closed", false, "Off: the game pauses and hides when the menu closes.\nOn: keys reach CS2 and Tetris at the same time - use the arrow scheme.")
    cmb(go, "tet_keys", "Controls", ITEMS.TET_KEYS, 1, "Arrows: left / right / down, Up or X rotate, Z rotate back, Space hard drop, C hold.\nWASD: A / D / S, W or K rotate, J rotate back, Space hard drop, L hold.\nP pauses, R restarts.")
    sld(go, "tet_level", "Start level", 1, 15, 1, "%d")
    chk(go, "tet_ghost", "Ghost piece", true)
    sld(go, "tet_scale", "Window scale", 60, 200, 100, "%d%%")
    sld(go, "tet_x", "Window X", 0, 100, 70, "%d%%")
    sld(go, "tet_y", "Window Y", 0, 100, 30, "%d%%")

    local gr = mk_group(tab, "Records")
    UI.tet_stats = lbl(gr, "best 0 · lines 0 · games 0")
    lbl(gr, "Guideline rules: 7-bag, SRS kicks, hold, lock delay, T-spins, combos, back-to-back.")
    btn(gr, "tet_wipe", "Reset records", "tet_wipe")
end

function BUILD.config()
    local chk, btn, lbl = W.chk, W.btn, W.lbl
    local tab = mk_tab("0x Config")

    local g = mk_group(tab, "Settings")
    chk(g, "persist_ui", "Remember settings (db)", true, "Stores this menu in data\\db and restores it on load.")
    chk(g, "notif", "Notifications", true)
    btn(g, "export", "Export settings", "export", "Writes data\\db\\0x_export.json, prints it to the console and copies it to the clipboard (Allow Insecure).")
    btn(g, "import_db", "Import data\\db\\0x_import.json", "import_db", "Loads a snapshot made by the web companion. Put the file into C:\\neverwin\\scripts\\data\\db.")
    UI.import_text = create(g, g.text, "import_text", "", "Snapshot (paste)", "")
    btn(g, "import_text", "Import pasted snapshot", "import_text", "Applies the JSON snapshot pasted into the field above.")
    btn(g, "reset_ui", "Reset settings to defaults", "reset_ui")

    local gd = mk_group(tab, "Data")
    UI.stats = lbl(gd, "tracked 0 · hits 0 · misses 0")
    btn(gd, "reset_learn", "Clear learned data", "reset_learn", "Forget every learned side and the hit / miss statistics.")

    local ga = mk_group(tab, "About")
    lbl(ga, META.name .. " v" .. META.version .. " · " .. META.credits)
    lbl(ga, "Tabs: Resolver · Rage · Anti-Aim · Visuals · Tetris · Config")
end

local function build_menu()
    local order = { "resolver", "rage", "antiaim", "visuals", "tetris", "config" }
    for i = 1, #order do
        local ok, err = pcall(BUILD[order[i]])
        if not ok then say("menu tab '" .. order[i] .. "' failed to build: " .. tostring(err)) end
    end
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
    if kind == "multi" then return not U.same(a, b) end
    return a ~= b
end

-- Converts a stored / imported value into a valid value for the element (nil = reject).
local function validate(r, v)
    local k = r.kind
    if k == "check" then
        if type(v) == "boolean" then return v end
    elseif k == "slider" then
        v = tonumber(v)
        if v then return clamp(floor(v + 0.5), r.lo, r.hi) end
    elseif k == "combo" then
        if type(v) == "string" then
            for i = 1, #r.items do
                if r.items[i] == v then return i end
            end
            return nil
        end
        v = tonumber(v)
        if v then return clamp(floor(v + 0.5), 1, #r.items) end
    elseif k == "color" then
        if type(v) == "table" and type(v.r) == "number" and type(v.g) == "number" and type(v.b) == "number" then
            return { r = clamp(v.r, 0, 255), g = clamp(v.g, 0, 255), b = clamp(v.b, 0, 255), a = clamp(tonumber(v.a) or 255, 0, 255) }
        end
    elseif k == "multi" then
        if type(v) == "table" then
            local m = {}
            for j = 1, #r.items do m[r.items[j]] = multi_on(v, j, r.items) end
            return m
        end
    end
    return nil
end

local function write_el(r, v)
    local el = r.el
    if is_dummy(el) then CFG[r.id] = v return end
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

local function notify(msg)
    if CFG.notif ~= false then pcall(client.notify, msg, META.name) end
    say(msg)
end

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

-- force = values came from load / reset / import / the preset itself: the preset is not
-- re-applied on top of them.
local function on_settings_changed(force)
    SET.dirty, SET.dirty_t = true, STATE.rt
    RB.eval_at = 0
    VIS.dirty = true
    AA.sync_menu()
    TET.sync_menu()
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

-- Runs before every button action (see W.btn): the regular poll is 50 / 400 ms, an action
-- that reads CFG right after a click must not see the value from before the last edit.
function ACT.sync()
    MENU.last = -1e9
    cfg_tick(false)
end

-- ---------------------------------------------------------------- persistence
local LEGACY_MAP = { enable = "rb_enable", debug = "log_cfg", ind_on = "panel", ind_x = "panel_x",
                     ind_y = "panel_y", ind_scale = "panel_scale", ind_color = "accent" }

-- Manual paths (code constants + snapshot) as sanitized string lists.
function IO.clean_paths(src)
    local out = { hc = {}, dmg = {}, safe = {}, baim = {}, hitbox = {} }
    if type(src) ~= "table" then return out end
    for id, list in pairs(out) do
        local s = src[id]
        if type(s) == "string" then s = { s } end
        if type(s) == "table" then
            for i = 1, #s do
                local p = s[i]
                -- a snapshot is untrusted input: bounded length, printable ASCII only
                if type(p) == "string" and #p <= 160 then
                    p = U.trim(p)
                    if p ~= "" and #list < 16 and not s_find(p, "[^\32-\126]") then list[#list + 1] = p end
                end
            end
        end
    end
    return out
end

function IO.pack()
    local t = {}
    for i = 1, #ORDER do
        local r = REG[ORDER[i]]
        local k, v = r.kind, CFG[r.id]
        if k == "check" or k == "slider" or k == "combo" then
            t[r.id] = v
        elseif k == "color" and type(v) == "table" then
            t[r.id] = { r = floor(v.r), g = floor(v.g), b = floor(v.b), a = floor(v.a or 255) }
        elseif k == "multi" and type(v) == "table" then
            local m = {}
            for j = 1, #r.items do m[r.items[j]] = multi_on(v, j, r.items) end
            t[r.id] = m
        end
    end
    local paths, any = {}, false
    for id, list in pairs(PATHS_USER) do
        if #list > 0 then paths[id], any = list, true end
    end
    return { v = META.schema, ver = META.version, persist = CFG.persist_ui ~= false, s = t, paths = any and paths or nil }
end

function IO.save()
    local ok, res = pcall(db.save, META.db_settings, IO.pack())
    return ok and res ~= false
end

-- Writes a snapshot table into the menu. Returns the number of applied values or nil, reason.
function IO.apply(data, legacy, only_persist)
    if type(data) ~= "table" or type(data.s) ~= "table" then return nil, "not a 0x snapshot" end
    local sv = tonumber(data.v)
    if sv and sv > META.schema then return nil, "snapshot was made by a newer 0x (schema " .. sv .. ")" end
    local n = 0
    PS.applying = true
    for id, v in pairs(data.s) do
        local tid = legacy and (LEGACY_MAP[id] or id) or id
        local r = REG[tid]
        if r and r.kind ~= "key" and (not only_persist or tid == "persist_ui") then
            local val = validate(r, v)
            if val ~= nil then
                write_el(r, val)
                n = n + 1
            end
        end
    end
    PS.applying = false
    if only_persist and REG.persist_ui then write_el(REG.persist_ui, false) end
    if type(data.paths) == "table" then PATHS_USER = IO.clean_paths(data.paths) end
    return n
end

function IO.load()
    local ok, data = pcall(db.load, META.db_settings, nil)
    local legacy, src = false, "v4"
    if not ok or type(data) ~= "table" or type(data.s) ~= "table" then
        ok, data = pcall(db.load, META.db_settings_v3, nil)
        src = "v3"
        if not ok or type(data) ~= "table" or type(data.s) ~= "table" then
            ok, data = pcall(db.load, META.db_legacy, nil)
            if not ok or type(data) ~= "table" or type(data.s) ~= "table" then return false end
            legacy, src = true, "s1"
        end
    end
    -- The user opted out of remembering settings: keep only that choice (v3 forgot it).
    if data.persist == false then
        IO.apply(data, legacy, true)
        return false
    end
    local n = IO.apply(data, legacy, false) or 0
    if src ~= "v4" and n > 0 then
        say("imported " .. n .. " settings from the " .. src .. " snapshot")
        SET.migrated = true
    end
    return n > 0
end

-- Applies an external snapshot (import) and makes it permanent.
function IO.import(data, origin)
    if type(data) ~= "table" then
        notify("Import failed (" .. origin .. "): not a JSON object")
        return
    end
    local n, why = IO.apply(data, false, false)
    if not n then
        notify("Import failed (" .. origin .. "): " .. tostring(why))
        return
    end
    PS.last = nil
    cfg_tick(true)
    SET.dirty, SET.dirty_t = true, -1e9
    if type(data.paths) == "table" then ACT.rescan() end
    notify(format("Imported %d settings from %s", n, origin))
end

function ACT.export()
    local snap = IO.pack()
    local ok, text = pcall(json.encode, snap)
    if not ok or type(text) ~= "string" then
        notify("Export failed: " .. tostring(text))
        return
    end
    local saved = safe(db.save, META.db_export, snap) ~= false
    say("snapshot: " .. text)
    local clip = false
    if safe(client.insecure) == true and utils and utils.clipboard_set then
        clip = pcall(utils.clipboard_set, text)
    end
    notify(format("Exported%s%s", saved and " to data\\db\\0x_export.json" or "", clip and " · copied to clipboard" or " · see console"))
end

function ACT.import_db()
    local ok, data = pcall(db.load, META.db_import, nil)
    if not ok or data == nil then
        notify("data\\db\\0x_import.json not found or not valid JSON")
        return
    end
    IO.import(data, "0x_import.json")
end

function ACT.import_text()
    local el = UI.import_text
    local s = el and not is_dummy(el) and safe(el.get, el) or nil
    if type(s) ~= "string" or U.trim(s) == "" then
        notify("Paste a snapshot into the field first")
        return
    end
    s = U.trim(s)
    if #s > META.import_max then
        notify(format("Snapshot rejected: %d bytes (limit %d)", #s, META.import_max))
        return
    end
    local brace = s_find(s, "{", 1, true)
    if brace and brace > 1 then s = s_sub(s, brace) end   -- tolerate a "0x:" style prefix
    local ok, data, err = pcall(json.decode, s)
    if not ok or data == nil then
        notify("Snapshot is not valid JSON: " .. tostring(ok and err or data))
        return
    end
    IO.import(data, "pasted snapshot")
    pcall(el.set, el, "")
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
    notify("Settings reset to defaults")
end

-- ============================================================================
--  RESOLVER
-- ============================================================================
RES.records, RES.by_pawn, RES.pending, RES.store = {}, {}, {}, {}
RES.insecure, RES.simtime_ok = false, true
RES.body_ok, RES.body_good, RES.body_bad = true, 0, 0
RES.last_purge, RES.store_dirty = 0, false
RES.stats = { shots = 0, hits = 0, heads = 0, misses = 0, resolver = 0, spread = 0, lagcomp = 0, moving = 0, airborne = 0, death = 0, lost = 0 }
RES.hw = { b = 1, fs = 1, mv = 1, md = 1 }                    -- hint reliability (session)
RES.runs = {}                                                 -- scratch: jitter run lengths
RES.write_cls, RES.write_ok, RES.write_fails = nil, nil, 0   -- write_ok: nil unknown, true working, false disabled
RES.focus = nil                                               -- record closest to the crosshair
RES.fs_skip = {}
RES.fs_opts = { skip = RES.fs_skip, mask = E.MASK_VISIBLE }

-- ---------------------------------------------------------------- records
-- SteamID for humans; controller address for bots (stable across respawns, unlike the pawn).
function RES.player_key(ctrl, pawn)
    if ctrl then
        local sid = safe(ctrl.steam_id, ctrl)
        if type(sid) == "string" and sid ~= "" and sid ~= "0" then return sid, true end
        local ca = safe(ctrl.address, ctrl)
        if ca then return "c" .. tostring(ca), false end
    end
    if pawn then
        local pa = safe(pawn.address, pawn)
        if pa then return "p" .. tostring(pa), false end
    end
    return nil, false
end

function RES.new_record(key, is_sid)
    local rec = {
        key = key, is_sid = is_sid, name = "?",
        -- history ring buffers
        yaws = {}, pitches = {}, deltas = {}, head = 0, n = 0, dhead = 0, dn = 0,
        pitch_jit = 0, p_avg = 0, pitch_kind = "",
        -- classification
        mode = "static", mode_conf = 0, center = 0, amp = 0, spin_rate = 0, mean_abs = 0, jit_alt = 0,
        mode_cand = nil, mode_cnt = 0,
        -- jitter model: cluster half range, switch period (updates), newest side and its run length
        jit_half = 0, jit_period = 1, jit_pconf = 0, jit_side = 1, jit_run = 0, jit_k = nil,
        -- hints
        body_delta = 0, body_ref = nil, b_hint = 0, fs_hint = 0, mv_hint = 0, md_hint = 0, score = 0, upd = 0,
        last_move_yaw = nil, last_move_t = 0, moving = false, speed = 0,
        -- lag compensation
        lc = false, lc_t = -1e9, last_origin = nil,
        -- learning
        side = 1, conf = 0.3, pred_side = 1, brute_idx = 1, manual = false,
        shots = 0, hits = 0, misses = 0, kills = 0, hit_streak = 0, miss_streak = 0,
        last_shot_t = -1e9, reveal_t = -1e9, last_reason = nil,
        prev_result = nil, hit_side = 0, ab_score = 0, ab_flips = 0, preflipped = false,
        -- output
        at_target = 0, raw_yaw = 0, raw_pitch = 0, amount = 0,
        resolved_yaw = 0, resolved_pitch = 0, resolved = false, applied = false,
        -- bookkeeping
        sim_time = nil, last_tick = -1, seen_rt = -1e9, pawn = nil, pawn_addr = nil, en_eye = nil,
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

function RES.get_record(ctrl, pawn, addr)
    local key, is_sid = RES.player_key(ctrl, pawn)
    if not key then return nil end
    local rec = RES.records[key]
    if not rec then
        rec = RES.extend(RES.new_record(key, is_sid))
        rec.name = (ctrl and safe(ctrl.name, ctrl)) or safe(pawn.name, pawn) or "?"
        RES.records[key] = rec
    end
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

function RES.record_by_controller(ctrl)
    if not ctrl then return nil end
    local key = RES.player_key(ctrl, nil)
    local rec = key and RES.records[key] or nil
    return rec or RES.record_by_pawn(safe(ctrl.pawn, ctrl))
end

function RES.remember(rec)
    if not rec.is_sid then return end
    RES.store[rec.key] = { side = rec.side, conf = rec.conf, hits = rec.hits, misses = rec.misses, t = os.time() }
    RES.store_dirty = true
end

function RES.store_load()
    local data, store = safe(db.load, META.db, {}), {}
    if type(data) == "table" then
        for k, v in pairs(data) do              -- the file is user-editable: keep well-formed entries only
            if type(k) == "string" and #k <= 32 and type(v) == "table" then
                store[k] = { side = (v.side == -1) and -1 or 1, conf = clamp(tonumber(v.conf) or 0, 0, 1),
                             hits = max(0, floor(tonumber(v.hits) or 0)), misses = max(0, floor(tonumber(v.misses) or 0)),
                             t = tonumber(v.t) or 0 }
            end
        end
    end
    RES.store = store
end

function RES.store_save(force)
    if not CFG.persist or (not RES.store_dirty and not force) then return end
    local list = {}
    for k, v in pairs(RES.store) do
        if type(v) == "table" then list[#list + 1] = { k = k, t = tonumber(v.t) or 0 }
        else RES.store[k] = nil end
    end
    if #list > C.DB_MAX then
        tsort(list, function(a, b) return a.t > b.t end)
        for i = C.DB_MAX + 1, #list do RES.store[list[i].k] = nil end
    end
    if safe(db.save, META.db, RES.store) ~= false then RES.store_dirty = false end
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
    if abs(sx) < 1e-6 and abs(sy) < 1e-6 then return rec.yaws[rec.head] end
    return normalize(deg(atan2(sy, sx)))
end

-- RES.jitter_model (two-cluster model) lives in the 4.2 additions below.
-- static / sway / jitter / spin / random from the delta window, plus a pitch class.
function RES.classify(rec)
    local dn = rec.dn
    if dn < 3 then
        rec.mode, rec.mode_conf = "static", 0
        return
    end
    local H, JMD = C.HISTORY, C.JITTER_MIN_DELTA
    local old_mode = rec.mode
    local small_sum, small_n = 0, 0
    local sum_abs, sum_signed, flips, big, prev_sign, alt, pairs_n = 0, 0, 0, 0, 0, 0, 0
    local prev_d
    local idx = (dn == H) and (rec.dhead % H + 1) or 1      -- oldest delta first
    local deltas = rec.deltas
    for _ = 1, dn do
        local d = deltas[idx]
        local ad = abs(d)
        sum_abs, sum_signed = sum_abs + ad, sum_signed + d
        if ad > JMD then
            big = big + 1
            local s = (d > 0) and 1 or -1
            if prev_sign ~= 0 and s ~= prev_sign then flips = flips + 1 end
            prev_sign = s
        else
            small_sum, small_n = small_sum + ad, small_n + 1
        end
        if prev_d then
            pairs_n = pairs_n + 1
            local m = max(ad, abs(prev_d))
            -- two consecutive deltas of equal size and opposite sign = two-way jitter
            if m > JMD * 0.5 and abs(d + prev_d) < max(4, 0.35 * m) then alt = alt + 1 end
        end
        prev_d = d
        idx = idx % H + 1
    end

    local mean_abs, mean_signed = sum_abs / dn, sum_signed / dn
    rec.mean_abs = mean_abs
    rec.jit_alt = (pairs_n > 0) and (alt / pairs_n) or 0

    if abs(mean_signed) > C.SPIN_MIN_RATE and big >= dn * 0.6 and flips <= 1 then
        rec.mode, rec.spin_rate, rec.mode_conf = "spin", mean_signed, min(1, big / dn)
    elseif (big >= dn * 0.4 and flips >= max(2, floor(big * 0.5)))
        -- delayed jitter: few big deltas, every one of them reverses the previous, quiet in between
        or (big >= 3 and flips >= big - 1 and (small_n == 0 or small_sum / small_n < 4)) then
        rec.mode = "jitter"
        rec.center = RES.circular_mean(rec)
        local amp = 0
        for i = 1, rec.n do amp = amp + abs(normalize(rec.yaws[i] - rec.center)) end
        rec.amp = amp / rec.n
        rec.mode_conf = min(1, (flips / max(1, big - 1)) * 0.5 + max(rec.jit_alt, 0.5) * 0.5)
        RES.jitter_model(rec)
    elseif mean_abs < C.STATIC_MAX_DELTA then
        rec.mode, rec.mode_conf = "static", 1 - mean_abs / C.STATIC_MAX_DELTA
    elseif mean_abs < C.SWAY_MAX_DELTA then
        rec.mode, rec.center, rec.mode_conf = "sway", RES.circular_mean(rec), 0.7
    else
        rec.mode, rec.center, rec.mode_conf = "random", RES.circular_mean(rec), 0.5
    end

    -- Hysteresis: a new class has to repeat before it replaces the current one.
    if rec.mode ~= old_mode and dn >= 6 then
        if rec.mode_cand == rec.mode then rec.mode_cnt = rec.mode_cnt + 1
        else rec.mode_cand, rec.mode_cnt = rec.mode, 1 end
        if rec.mode_cnt < C.MODE_CONFIRM then rec.mode = old_mode end
    else
        rec.mode_cand, rec.mode_cnt = nil, 0
    end
    if rec.mode ~= "jitter" then rec.jit_pconf = 0 end

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
        local c = type(h) == "table" and h.center or nil
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

-- Model yaw from hitboxes. Read every BODY_EVERY updates; the delta to the CURRENT eye yaw
-- is recomputed every update so the cached reference stays valid under jitter.
function RES.body_hint(rec, pawn, yaw, refresh)
    if not RES.body_ok then return 0 end
    if refresh or rec.body_ref == nil then
        local hbs = safe(pawn.hitboxes, pawn)
        if type(hbs) ~= "table" then
            RES.body_bad = RES.body_bad + 1
            if RES.body_bad > 40 and RES.body_good == 0 then RES.body_ok = false end
            return 0
        end
        rec.body_ref = pair_yaw(hbs, "ll", "rl") or pair_yaw(hbs, "la", "ra")
    end
    local ref = rec.body_ref
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
    local yaw = rad(U.yaw_to(lp_eye, en_eye))
    local rx, ry = sin(yaw) * C.FS_OFFSET, -cos(yaw) * C.FS_OFFSET
    RES.fs_skip[1], RES.fs_skip[2] = lp, pawn
    local tl = safe(trace.line, lp_eye, vector(en_eye.x - rx, en_eye.y - ry, en_eye.z), RES.fs_opts)
    local tr = safe(trace.line, lp_eye, vector(en_eye.x + rx, en_eye.y + ry, en_eye.z), RES.fs_opts)
    RES.fs_skip[1], RES.fs_skip[2] = nil, nil
    if type(tl) ~= "table" or type(tr) ~= "table" then return 0 end
    local bl, br = (tonumber(tl.fraction) or 1) < 0.98, (tonumber(tr.fraction) or 1) < 0.98
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
    return (CFG.brute_pat == E.PAT_STEP) and #STEP_SEQ or #BRUTE
end

-- Multiplier and absolute amount for a brute index (defaults to the record's current index).
function RES.brute_entry(rec, idx)
    local m = CFG.mode
    if m == E.MODE_STATIC or m == E.MODE_OFFSET then return 1, CFG.desync end
    idx = idx or rec.brute_idx
    if CFG.brute_pat == E.PAT_STEP then
        local i = (idx - 1) % #STEP_SEQ + 1
        return STEP_SEQ[i], STEP_SEQ[i] * CFG.brute_step
    end
    local i = (idx - 1) % #BRUTE + 1
    return BRUTE[i], BRUTE[i] * CFG.desync
end

function RES.decide_side(rec, b, fs, mv, md)
    rec.b_hint, rec.fs_hint, rec.mv_hint, rec.md_hint = b, fs, mv, md
    if rec.manual or CFG.mode == E.MODE_BRUTE or CFG.mode == E.MODE_OFFSET then
        rec.score, rec.pred_side = rec.side, rec.side
        return
    end
    local score = rec.side * rec.conf * C.W_LEARNED + RES.class_bias(rec)
    local hw = RES.hw
    if CFG.body then score = score + b * C.W_BODY * hw.b end
    if CFG.freestand then score = score + fs * C.W_FREESTAND * hw.fs end
    if CFG.move_mem then score = score + mv * C.W_MOVE * hw.mv end
    if CFG.move_dir then score = score + md * C.W_MOVEDIR * hw.md end
    rec.score = score
    if abs(score) >= C.SIDE_DEADZONE then
        rec.pred_side = (score > 0) and 1 or -1
    end
end

function RES.resolve_pitch(rec, pitch)
    local pm = CFG.pitch
    if pm == E.PITCH_OFF then return pitch end
    if pm == E.PITCH_CLAMP then return clamp(pitch, -89, 89) end
    if pm == E.PITCH_DOWN then return 89 end
    if pm == E.PITCH_ZERO then return 0 end
    if pm == E.PITCH_UP then return -89 end
    if pitch > 89.5 then return 89 end
    if pitch < -89.5 then return -89 end
    if rec.pitch_jit >= 3 then return 89 end          -- fake-pitch flicker: assume looking down
    return clamp(pitch, -89, 89)
end

function RES.compute(rec, yaw, pitch)
    local mode, m = rec.mode, CFG.mode
    local at = rec.at_target

    if m == E.MODE_OFFSET then
        rec.amount = CFG.yaw_off
        rec.resolved_yaw = normalize(at + CFG.yaw_off)
        rec.resolved_pitch = RES.resolve_pitch(rec, pitch)
        rec.resolved = true
        return
    end

    rec.jit_k = nil
    if mode == "jitter" and (m == E.MODE_ADAPTIVE or m == E.MODE_JITSPIN) then
        local jm = CFG.jit_mode
        if jm == E.JIT_FOLLOW then
            rec.amount, rec.resolved_yaw = 0, yaw
            rec.resolved_pitch = RES.resolve_pitch(rec, pitch)
            rec.resolved = true
            return
        end
        if rec.jit_pconf >= C.JIT_PRED_CONF and rec.jit_half > 0 then
            local seq = JIT_SEQ[(jm == E.JIT_PREDICT) and 2 or 1]
            local k = seq[(rec.brute_idx - 1) % #seq + 1]
            -- the newest side has lasted a full period: the next update is on the other side
            local nxt = (rec.jit_run >= rec.jit_period) and -rec.jit_side or rec.jit_side
            local off = nxt * rec.jit_half * k
            rec.jit_k, rec.amount = k, off
            rec.resolved_yaw = normalize(rec.center + off)
            rec.resolved_pitch = RES.resolve_pitch(rec, pitch)
            rec.resolved = true
            return
        end
    end

    local base
    if CFG.base == E.BASE_TARGET then
        base = at
    elseif CFG.base == E.BASE_EYE then
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
    if m == E.MODE_JITSPIN then
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
    elseif mode == "spin" and m == E.MODE_JITSPIN then
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
-- Returns false or a reason tag ("LC" / "RES").
function RES.unresolved(rec)
    if not rec or not rec.resolved then return false end
    if rec.lc then return "LC" end
    if rec.manual then return false end
    if rec.miss_streak >= 2 or rec.brute_idx >= 3 then return "RES" end
    if rec.mode == "random" and rec.conf < 0.5 then return "RES" end
    if rec.mode == "jitter" and rec.amp > 35 and rec.conf < 0.5 then return "RES" end
    return false
end

-- ---------------------------------------------------------------- memory write
function RES.can_write()
    return CFG.apply and RES.insecure and RES.write_ok ~= false
end

function RES.apply(pawn, rec)
    rec.applied = false
    if not RES.can_write() then return end
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
    notify("m_angEyeAngles not writable (schema / insecure); tracking only")
end

function RES.read_simtime(pawn)
    if not RES.simtime_ok then return nil end
    local ok, v = pcall(pawn.get, pawn, "C_BaseEntity", "m_flSimulationTime", "float")
    if ok and type(v) == "number" then return v end
    RES.simtime_ok = false
    return nil
end

-- ---------------------------------------------------------------- per-player update
function RES.process(pawn, ctrl, addr, lp, lp_alive, lp_eye, now, tick, rt)
    local rec = RES.get_record(ctrl, pawn, addr)
    if not rec then return nil end
    local gap = rt - rec.seen_rt                 -- > 0.25 s: dormant / respawned in between
    rec.seen_rt = rt

    local eye = pawn:eye_angles()
    local yaw, pitch = normalize(eye.y), eye.x

    -- Freshness gate: only analyse genuinely new network data.
    local simt = RES.read_simtime(pawn)
    local fresh
    if simt then
        if CFG.lc_detect and rec.sim_time and gap < 0.25 and simt < rec.sim_time - 1e-4 then
            rec.lc_t = now                       -- simulation time went backwards: tickbase shift
        end
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

    -- The LC flag must expire even while no fresh data arrives (dormant / frozen target).
    local lc_age = now - rec.lc_t
    rec.lc = CFG.lc_detect and lc_age >= 0 and lc_age < C.LC_HOLD
    -- A sample right after the enemy fired carries his aim yaw, not his anti-aim. A negative
    -- age means the clock was reset: the stamp is stale and must not freeze the record.
    local reveal_age = now - rec.reveal_t
    if not fresh or (reveal_age >= 0 and reveal_age < C.REVEAL_TIME) then
        if rec.resolved then RES.apply(pawn, rec) end
        return rec
    end
    if gap > 0.25 then
        rec.n, rec.dn, rec.head, rec.dhead = 0, 0, 0, 0       -- stale history must not mix in
        rec.last_origin, rec.body_ref, rec.fs_cache = nil, nil, nil
        rec.pitch_jit, rec.jit_pconf, rec.mode_cand, rec.mode_cnt = 0, 0, nil, 0
    end
    rec.upd = rec.upd + 1

    local origin = pawn:origin()
    if CFG.lc_detect and origin and rec.last_origin then
        local dx, dy, dz = origin.x - rec.last_origin.x, origin.y - rec.last_origin.y, origin.z - rec.last_origin.z
        if dx * dx + dy * dy + dz * dz > C.LC_DIST_SQR then rec.lc_t = now end
    end
    rec.last_origin = origin
    rec.lc = CFG.lc_detect and (now - rec.lc_t) < C.LC_HOLD and (now - rec.lc_t) >= 0
    -- Angles received right after an LC break are not his anti-aim: keep the last stable result.
    if rec.lc and CFG.lc_hold and rec.resolved and (now - rec.lc_t) < C.LC_FREEZE then
        RES.apply(pawn, rec)
        return rec
    end

    local vel = pawn:velocity()
    local speed = vel:length2d()
    rec.raw_yaw, rec.raw_pitch, rec.speed = yaw, pitch, speed
    RES.push_history(rec, yaw, pitch)
    RES.classify(rec)

    if speed > C.MOVE_SPEED then
        rec.moving = true
        rec.last_move_yaw = normalize(deg(atan2(vel.y, vel.x)))
        rec.last_move_t = now
    else
        rec.moving = false
    end

    local en_eye = pawn:eye_position()
    rec.en_eye = en_eye
    rec.at_target = normalize(U.yaw_to(en_eye, lp_eye))

    local b = CFG.body and RES.body_hint(rec, pawn, yaw, rec.upd % C.BODY_EVERY == 0) or 0
    local fs = 0
    if CFG.freestand and lp_alive then
        if rec.fs_cache == nil or rec.upd % C.FS_EVERY == 1 then
            rec.fs_cache = RES.freestand_hint(lp, pawn, lp_eye, en_eye)
        end
        fs = rec.fs_cache or 0
    end
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
function RES.log(kind, text)
    VIS.push(kind, text)
    if CFG.log_hits then say(text) end
end

-- Spread cone sample, refreshed every createmove. At weapon_fire the smaller of the last two
-- samples is used: at least one of them predates the shot's own accuracy penalty.
function RES.sample_spread(lp)
    if not (CFG.enable and CFG.feedback and CFG.spread_blame) then
        STATE.inacc, STATE.inacc_prev = nil, nil
        return
    end
    local info = safe(lp.weapon_info, lp)
    local v = nil
    if type(info) == "table" then
        local ia, sp = tonumber(info.inaccuracy), tonumber(info.spread)
        if ia and sp and ia >= 0 and sp >= 0 and ia + sp < 1 then v = ia + sp end
    end
    STATE.inacc_prev, STATE.inacc = STATE.inacc, v
end

function RES.is_local_controller(ctrl)
    if not ctrl then return false end
    local lc = entity.local_controller()
    if not lc then return false end
    return safe(ctrl.address, ctrl) == lc:address()
end

-- Target of our shot. Returns record, on_target (the shot ray really crossed his model).
function RES.find_shot_target(lp)
    local from = safe(lp.eye_position, lp)
    if not from then return nil, false end
    local a1, a2 = STATE.cmd_angles, safe(engine.view_angles)    -- sent angles first (silent aim)
    for i = 1, 2 do
        local a = (i == 1) and a1 or a2
        if a then
            local r = safe(trace.bullet, from, from + a:forward() * 8192)
            if type(r) == "table" and r.hit and r.entity then
                local rec = RES.record_by_pawn(r.entity)
                if rec then return rec, true end
            end
        end
    end
    -- ragebot assist target (closest to the crosshair, already filtered)
    if RB.t_addr then
        local rec = RES.by_pawn[RB.t_addr]
        if rec then return rec, false end
    end
    -- fallback: closest tracked enemy within 12 degrees
    local va = a1 or a2
    if not va then return nil, false end
    local best, best_fov = nil, 12
    local rt = globals.realtime()
    for _, rec in pairs(RES.records) do
        if rec.en_eye and rt - rec.seen_rt < 0.2 then
            local fov = U.fov(from, rec.en_eye, va)
            if fov < best_fov then best, best_fov = rec, fov end
        end
    end
    return best, false
end

function RES.on_weapon_fire(ev)
    if not CFG.enable then return end
    local ctrl = safe(ev.get_controller, ev, "userid")
    if not ctrl then return end
    if not RES.is_local_controller(ctrl) then
        local rec = RES.record_by_pawn(safe(ev.get_pawn, ev, "userid")) or RES.record_by_controller(ctrl)
        if rec then rec.reveal_t = globals.curtime() end
        return
    end
    if not CFG.feedback then return end
    if WPN.non_gun_name(safe(ev.get_string, ev, "weapon")) then return end
    local lp = entity.local_pawn()
    if not lp then return end
    local info = safe(lp.weapon_info, lp)
    if type(info) == "table" and info.gun == false then return end

    local rec, on_target = RES.find_shot_target(lp)
    if not rec then return end
    local now = globals.curtime()
    rec.shots = rec.shots + 1
    RES.stats.shots = RES.stats.shots + 1
    if now - rec.last_shot_t < C.SHOT_DEDUPE then return end   -- spray: one pending shot per slice
    rec.last_shot_t = now

    local cone = nil
    local a, b = STATE.inacc, STATE.inacc_prev
    local s = (a and b) and min(a, b) or a or b
    if s and rec.en_eye then
        local from = safe(lp.eye_position, lp)
        if from then cone = s * from:dist(rec.en_eye) end
    end
    local pending = RES.pending
    pending[#pending + 1] = {
        key = rec.key, t = now, side = rec.pred_side, idx = rec.brute_idx, mode = rec.mode,
        moving = rec.moving, lp_air = STATE.lp_air, baim = RB.baim ~= nil, lc = rec.lc,
        cone = cone, on_target = on_target, jit = rec.jit_k ~= nil,
        h = { b = sign(rec.b_hint), fs = sign(rec.fs_hint), mv = sign(rec.mv_hint), md = sign(rec.md_hint) },
    }
    if #pending > C.PENDING_MAX then tremove(pending, 1) end
end

-- Oldest pending shot of this target. If there is none, the most recent uncertain shot
-- (attributed without a ray hit) is dropped: it went to this player, not to the guessed one.
function RES.take_pending(key)
    local pending = RES.pending
    for i = 1, #pending do
        if pending[i].key == key then return tremove(pending, i) end
    end
    for i = #pending, 1, -1 do
        if not pending[i].on_target then
            tremove(pending, i)
            break
        end
    end
    return nil
end

-- Hints that agreed with the confirmed side gain weight, the others lose it.
function RES.learn_hints(shot, truth)
    if not CFG.hint_learn or not shot or not shot.h or truth == 0 then return end
    local hw = RES.hw
    for k, v in pairs(shot.h) do
        if v ~= 0 then
            if v == truth then hw[k] = min(C.HW_MAX, hw[k] + C.HW_GAIN)
            else hw[k] = max(C.HW_MIN, hw[k] - C.HW_LOSS) end
        end
    end
end

function RES.on_hit(rec, hitgroup, dmg)
    local shot = RES.take_pending(rec.key)
    rec.hits, rec.hit_streak, rec.miss_streak = rec.hits + 1, rec.hit_streak + 1, 0
    local st = RES.stats
    st.hits = st.hits + 1

    local head = (hitgroup == K.HG_HEAD)
    if head then st.heads = st.heads + 1 end
    local partial = CFG.body_partial and not head and not (shot and shot.baim)
    local used_side = shot and shot.side or rec.pred_side
    local m = RES.brute_entry(rec, shot and shot.idx or nil)   -- multiplier that was live at fire time
    local jit = shot and shot.jit                              -- jitter model shot: the index that hit stays
    if not partial and m ~= 0 and not jit then
        rec.side = sign(used_side * m)
        if CFG.brute_pat ~= E.PAT_STEP and abs(m) == 1 then rec.brute_idx = 1 end
        RES.learn_hints(shot, rec.side)
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

    RES.note_hit(rec, shot, not partial and m ~= 0 and not jit)
    local pre = ""
    if CFG.anti_ab and rec.ab_score >= 2 and not partial then
        rec.side = -rec.side                      -- he will flip after this hit: be there first
        rec.ab_flips = rec.ab_flips + 1
        rec.preflipped = true
        pre = "  · pre-flip"
    end
    rec.last_reason = nil
    RES.remember(rec)
    RES.log(head and "hit" or "body", format("%s  %s %d%s%s", rec.name, head and "HEAD" or "BODY",
        floor(tonumber(dmg) or 0), partial and " (partial)" or "", pre))
end

function RES.miss_reason(shot, rec)
    if STATE.lp_dead then return "death" end                  -- we died before the shot could register
    if STATE.rt - rec.seen_rt > 0.25 then return "lost" end   -- target went dormant / left
    if shot.lc then return "lagcomp" end
    if shot.lp_air then return "airborne" end
    if shot.moving then return "moving" end
    if CFG.spread_blame and shot.cone and shot.cone > C.SPREAD_BLAME then return "spread" end
    return "resolver"
end

function RES.on_miss(shot, rec)
    local st = RES.stats
    local reason = RES.miss_reason(shot, rec)
    rec.misses, rec.hit_streak, rec.last_reason = rec.misses + 1, 0, reason
    st.misses = st.misses + 1
    st[reason] = (st[reason] or 0) + 1

    if reason ~= "resolver" then
        -- not the resolver's fault: no brute step, no anti-bruteforce bookkeeping
        rec.conf = max(0, rec.conf - C.SOFT_CONF_LOSS)
        RES.remember(rec)
        RES.log("miss", format("%s  MISS (%s)", rec.name, reason))
        return
    end

    rec.conf = max(0, rec.conf - C.MISS_CONF_LOSS)
    local prev = rec.prev_result
    rec.prev_result = "miss"
    rec.manual = false
    if prev == "hit" and CFG.anti_ab then
        if rec.preflipped then
            rec.ab_score = max(0, rec.ab_score - 1)   -- the pre-flip was wrong
            rec.preflipped = false
        elseif shot.side == rec.hit_side then
            rec.ab_score = min(3, rec.ab_score + 1)   -- same side missed right after a hit: he flipped
        end
    end
    rec.miss_streak = rec.miss_streak + 1
    if not shot.jit then
        local bm = RES.brute_entry(rec, shot.idx)
        if abs(bm) == 1 then
            local wrong = sign(shot.side * bm)
            RES.learn_hints(shot, -wrong)                                        -- the other side was right
            RES.note_miss(rec, shot, wrong)
        end
    end
    local info = ""
    if rec.miss_streak >= CFG.miss_tol then
        rec.miss_streak = 0
        if CFG.mode == E.MODE_STATIC or CFG.mode == E.MODE_OFFSET then
            rec.side = -rec.side
            info = "  -> flip"
        elseif shot.idx == rec.brute_idx then            -- step once per brute index, not per queued shot
            rec.brute_idx = RES.next_brute(rec, shot)
            info = format("  -> brute %d", rec.brute_idx)
        end
    end
    RES.remember(rec)
    RES.log("miss", format("%s  MISS (resolver)%s", rec.name, info))
end

function RES.check_pending(now)
    local pending = RES.pending
    local win = CFG.miss_win_s or 0.35
    for i = #pending, 1, -1 do
        local s = pending[i]
        if now - s.t > win then
            tremove(pending, i)
            local rec = RES.records[s.key]
            if rec then RES.on_miss(s, rec) end
        elseif now < s.t then
            tremove(pending, i)   -- clock went backwards (map change)
        end
    end
end

function RES.on_player_hurt(ev)
    if not CFG.enable or not CFG.feedback then return end
    local lc = entity.local_controller()
    if not lc then return end
    local la = lc:address()
    local att = safe(ev.get_controller, ev, "attacker")
    local vic = safe(ev.get_controller, ev, "userid")
    local att_a = att and safe(att.address, att) or nil
    local vic_a = vic and safe(vic.address, vic) or nil
    local bullet = not WPN.non_gun_name(safe(ev.get_string, ev, "weapon"))   -- grenades / fire / knife do not teach

    if att_a == la then
        if not bullet or vic_a == la then return end
        local rec = RES.record_by_pawn(safe(ev.get_pawn, ev, "userid")) or RES.record_by_controller(vic)
        if not rec then return end
        RES.on_hit(rec, safe(ev.get_int, ev, "hitgroup") or 0, safe(ev.get_int, ev, "dmg_health") or 0)
    elseif CFG.flip_on_hurt and bullet and att and vic_a == la then
        local rec = RES.record_by_pawn(safe(ev.get_pawn, ev, "attacker")) or RES.record_by_controller(att)
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
    rec.jit_pconf, rec.jit_k, rec.mode_cand, rec.mode_cnt = 0, nil, nil, 0
    rec.resolved, rec.applied, rec.manual = false, false, false
    rec.sim_time, rec.last_move_yaw, rec.last_origin = nil, nil, nil
    rec.body_ref, rec.fs_cache, rec.lc, rec.lc_t = nil, nil, false, -1e9
    rec.miss_streak = 0
    if rec.tried then
        for k in pairs(rec.tried) do rec.tried[k] = nil end
    end
end

function RES.on_player_death(ev)
    if not CFG.enable then return end
    local rec = RES.record_by_pawn(safe(ev.get_pawn, ev, "userid"))
        or RES.record_by_controller(safe(ev.get_controller, ev, "userid"))
    if not rec then return end
    local pending = RES.pending
    for i = #pending, 1, -1 do
        if pending[i].key == rec.key then tremove(pending, i) end
    end
    RES.reset_history(rec)
    if RES.focus == rec then RES.focus = nil end
    local att = safe(ev.get_controller, ev, "attacker")
    if att and RES.is_local_controller(att) then
        rec.kills = rec.kills + 1
        RES.log("kill", format("%s  KILL  (%d/%d)", rec.name, rec.hits, rec.misses))
    end
end

-- Manual override: rising edge of the flip bind inverts the crosshair target's side.
function RES.check_flip()
    if STATE.kb_captured then return end        -- Tetris is reading the keyboard
    local on = bind_on(UI.k_flip)
    if on == STATE.flip_prev then return end
    STATE.flip_prev = on
    if not on then return end
    local rec = RES.focus
    if not rec then return end
    rec.side = -rec.pred_side
    rec.pred_side = rec.side
    rec.conf = max(rec.conf, 0.6)
    rec.manual, rec.brute_idx, rec.miss_streak = true, 1, 0
    RES.remember(rec)
    RES.log("info", format("%s  manual flip -> %s", rec.name, rec.side > 0 and "L" or "R"))
end

-- ---------------------------------------------------------------- frame stage
-- After lag compensation the game may restore the networked angles: write them again.
-- Fresh pawns are fetched every time (never a cached pointer); skipped entirely if no write is possible.
function RES.reapply_all()
    if not RES.can_write() then return end
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
            if RES.focus == rec then RES.focus = nil end
            RES.records[key] = nil
        end
    end
end

function RES.frame(st)
    if st ~= E.STAGE_NET_END and st ~= E.STAGE_LAGCOMP then return end
    cfg_tick(false)
    if not CFG.enable or not engine.in_game() then
        RES.focus = nil
        return
    end
    if st == E.STAGE_LAGCOMP then
        RES.reapply_all()
        return
    end
    RES.insecure = safe(client.insecure) == true
    STATE.insecure = RES.insecure

    local lp = entity.local_pawn()
    if not lp then return end
    local lp_alive = safe(lp.alive, lp) == true
    local lp_eye = safe(lp.eye_position, lp)
    if not lp_eye then return end

    local now, tick, rt = globals.curtime(), globals.tickcount(), STATE.rt
    local va = safe(engine.view_angles)
    local players = safe(entity.players)
    if type(players) ~= "table" then return end
    local focus, focus_fov = nil, C.FOCUS_FOV
    for i = 1, #players do
        local p = players[i]
        local pawn = p.pawn
        if pawn and pawn:alive() and pawn:is_enemy() then
            local ok, rec = pcall(RES.process, pawn, p.controller, pawn:address(), lp, lp_alive, lp_eye, now, tick, rt)
            if not ok then
                if CFG.debug then report("process", rec) end
            elseif rec and va and rec.en_eye then
                local fov = U.fov(lp_eye, rec.en_eye, va)
                if fov < focus_fov then focus, focus_fov = rec, fov end
            end
        end
    end
    RES.focus = focus
    RES.check_flip()

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
    for k in pairs(RES.stats) do RES.stats[k] = 0 end
    for k in pairs(RES.hw) do RES.hw[k] = 1 end
    RES.focus, RES.store_dirty = nil, false
    safe(db.save, META.db, {})
    notify("Learned data cleared")
end

function RES.on_round_start()
    RES.reset_volatile()
    RES.store_save(false)
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
    RES.store_save(false)
    RES.records, RES.by_pawn, RES.pending = {}, {}, {}
    RES.focus = nil
end

-- ============================================================================
--  RESOLVER · 4.2 additions
--    · two-cluster jitter model (1-D 2-means on the circle, tightness-weighted confidence)
--    · side memory per AA class
--    · blacklist of effective offsets that just missed
--    · continuous trust score (drives the headshot assist)
-- ============================================================================
C.TRIED_TTL = 20      -- s; a missed effective offset is not tried again for this long
C.W_CLASS   = 0.50    -- weight of the per-class side memory in the side score
C.CLS_GAIN  = 0.34    -- class memory gain per confirmed hit
C.CLS_LOSS  = 0.25    -- class memory loss per resolver miss

-- Fields added in 4.2 (kept out of new_record so the v4.1 record layout stays readable).
function RES.extend(rec)
    rec.tried, rec.cls, rec.good_idx, rec.jit_tight = {}, {}, nil, 0
    return rec
end

-- Two-angle jitter model. The split point is refined like 1-D 2-means: clusters are the samples
-- on either side of the current center, the center moves to the midpoint of both cluster means.
-- Tightness (how close the samples sit to +-half) scales the prediction confidence, so 3-way /
-- random patterns that only look like jitter fall back to the center handling.
function RES.jitter_model(rec)
    local H, n, yaws, c0 = C.HISTORY, rec.n, rec.yaws, rec.center
    local hi, lo = 0, 0
    for _ = 1, 3 do
        local hs, hn, ls, ln = 0, 0, 0, 0
        for i = 1, n do
            local o = normalize(yaws[i] - c0)
            if o >= 0 then hs, hn = hs + o, hn + 1 else ls, ln = ls + o, ln + 1 end
        end
        if hn == 0 or ln == 0 then
            rec.jit_pconf = 0
            return
        end
        hi, lo = hs / hn, ls / ln
        local shift = (hi + lo) * 0.5
        c0, hi, lo = normalize(c0 + shift), hi - shift, lo - shift
        if abs(shift) < 0.5 then break end
    end
    local half = (hi - lo) * 0.5
    local dev = 0
    for i = 1, n do dev = dev + abs(abs(normalize(yaws[i] - c0)) - half) end
    local tight = clamp(1 - (dev / n) / max(4, half * 0.5), 0, 1)
    rec.center, rec.jit_half, rec.amp, rec.jit_tight = c0, half, half, tight

    local idx = (n == H) and (rec.head % H + 1) or 1        -- oldest sample first
    local side, run, runs, rn = 0, 0, RES.runs, 0
    for _ = 1, n do
        local sd = (normalize(yaws[idx] - c0) >= 0) and 1 or -1
        if sd == side then
            run = run + 1
        else
            if side ~= 0 then rn = rn + 1 runs[rn] = run end
            side, run = sd, 1
        end
        idx = idx % H + 1
    end
    local first = (rn >= 3) and 2 or 1                       -- the oldest run is cut by the window
    local total = rn - first + 1
    local best, best_n = 1, 0
    for p = 1, C.JIT_MAX_PERIOD do
        local cnt = 0
        for i = first, rn do
            if runs[i] == p then cnt = cnt + 1 end
        end
        if cnt > best_n then best, best_n = p, cnt end
    end
    rec.jit_period, rec.jit_side, rec.jit_run = best, side, run
    rec.jit_pconf = (total >= 2) and (best_n / total) * (0.5 + 0.5 * tight) or 0
end

-- Effective signed offset of a brute entry, as a table key (side x multiplier, 1/100 steps).
function RES.eff_key(side, mult) return floor(side * mult * 100 + 0.5) end

-- Next brute index after a resolver miss. Entries whose effective offset missed within
-- TRIED_TTL are skipped; when all of them failed the memory is cleared and the list restarts
-- at the entry that hit last (or simply at the next one).
function RES.next_brute(rec, shot)
    local len, now, tried = RES.brute_len(), STATE.rt, rec.tried
    tried[RES.eff_key(shot.side, (RES.brute_entry(rec, shot.idx)))] = now
    local idx = rec.brute_idx
    if not CFG.brute_skip then return idx % len + 1 end
    for _ = 1, len do
        idx = idx % len + 1
        local t = tried[RES.eff_key(rec.pred_side, (RES.brute_entry(rec, idx)))]
        if not t or now - t >= C.TRIED_TTL or now < t then return idx end
    end
    for k in pairs(tried) do tried[k] = nil end
    local good = rec.good_idx
    if good and good ~= rec.brute_idx and good <= len then return good end
    return rec.brute_idx % len + 1
end

-- Confirmed (non partial) hit: the class that was live at fire time learns the side.
function RES.note_hit(rec, shot, confirmed)
    if not confirmed then return end
    rec.good_idx = shot and shot.idx or rec.brute_idx
    local mode = shot and shot.mode or rec.mode
    local c = rec.cls[mode]
    if not c then
        c = { side = rec.side, w = 0 }
        rec.cls[mode] = c
    end
    if c.side ~= rec.side then c.side, c.w = rec.side, 0 end
    c.w = min(1, c.w + C.CLS_GAIN)
    for k in pairs(rec.tried) do rec.tried[k] = nil end
end

-- Resolver miss with a full-desync entry: the class memory for that side weakens.
function RES.note_miss(rec, shot, wrong_side)
    local c = rec.cls[shot.mode or rec.mode]
    if c and c.side == wrong_side then c.w = max(0, c.w - C.CLS_LOSS) end
end

function RES.class_bias(rec)
    if not CFG.cls_mem then return 0 end
    local c = rec.cls[rec.mode]
    if not c then return 0 end
    return c.side * c.w * C.W_CLASS
end

-- How much the current guess can be trusted, 0..1. One number for the panel, the debug view
-- and the headshot assist; RES.unresolved stays the hard "do not trust" gate.
function RES.trust(rec)
    if not rec or not rec.resolved or rec.lc then return 0 end
    local t = 0.25 + rec.conf * 0.45
    local mode = rec.mode
    if mode == "static" then t = t + 0.20 * rec.mode_conf
    elseif mode == "sway" then t = t + 0.08
    elseif mode == "jitter" then t = t + ((rec.jit_k ~= nil) and 0.18 * rec.jit_pconf or -0.10)
    elseif mode == "spin" then t = t - 0.10
    else t = t - 0.20 end
    local c = rec.cls[mode]
    if c and c.side == rec.pred_side then t = t + 0.10 * c.w end
    t = t + min(0.15, rec.hit_streak * 0.05) - min(0.30, rec.miss_streak * 0.15) - min(0.20, (rec.brute_idx - 1) * 0.05)
    if rec.moving then t = t - 0.05 end
    if rec.manual then t = max(t, 0.6) end
    return clamp(t, 0, 1)
end

-- ============================================================================
--  RAGE ASSIST
--  There is no ragebot module in the API, so values are read and written through
--  config.get / config.set. Paths are discovered from config.keys; originals are
--  journaled in db and returned when the assist stands down.
-- ============================================================================
RB.tick_n, RB.cm_t, RB.paint_t, RB.hk_t, RB.store_t = 0, -1e9, -1e9, -1e9, 0
RB.air_ticks, RB.land_soon, RB.sim_fail, RB.sim_disabled, RB.g_tick = 0, false, 0, false, K.GRAVITY * 0.015625
RB.state, RB.wgroup, RB.waddr, RB.wtick, RB.eval_at = nil, nil, nil, -1e9, 0
RB.t_hp, RB.t_air, RB.t_move, RB.t_addr, RB.t_unres = nil, false, false, nil, false
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
    local v = U.copy(orig)
    Journal.data[path] = v
    if not U.same(Journal.disk[path], v) then Journal.add_dirty = true end
end

function Journal.remove(path)
    if Journal.data[path] == nil then return end
    Journal.data[path] = nil
    if Journal.disk[path] ~= nil then Journal.rm_dirty, Journal.rm_t = true, STATE.rt end
end

function Journal.missing()
    for k, v in pairs(Journal.data) do
        if not U.same(Journal.disk[k], v) then return true end
    end
    return false
end

function Journal.stale()
    for k in pairs(Journal.disk) do
        if Journal.data[k] == nil then return true end
    end
    return false
end

function Journal.flush(force)
    local need = false
    if Journal.add_dirty then
        need = Journal.missing()
        if not need then Journal.add_dirty = false end
    end
    if not need and Journal.rm_dirty and (force or STATE.rt - Journal.rm_t >= K.JOURNAL_LAZY) then
        need = Journal.stale()
        if not need then Journal.rm_dirty = false end
    end
    if not need then return end
    if not force and STATE.rt - SET.io_t < K.IO_RETRY then return end
    local ok, res = pcall(db.save, META.db_journal, Journal.data)
    if ok and res ~= false then
        local disk = {}
        for k, v in pairs(Journal.data) do disk[k] = U.copy(v) end
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
            Journal.disk[path] = U.copy(val)
            local cur = cfg_get(path)
            if cur ~= nil and type(cur) == type(val) and not U.same(cur, val) then
                if cfg_set(path, val) then
                    n = n + 1
                else
                    Journal.data[path] = U.copy(val)
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
Bind.HEAD = {}           -- "hitbox list narrowed to the head" (headshot assist)

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

function Bind.tags_for(low)
    local tags
    for i = 1, #PATH_TAGS do
        if U.any_match(low, PATH_TAGS[i][2]) then
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
    sl.recs[sl.n] = { path = path, tags = Bind.tags_for(s_lower(path)), orig = NONE, cur = nil, want = nil,
                      eff = false, bad = 0, mism = 0, dead = false, warned = false, ro = false }
    return true
end

function Bind.fail(sl, rec, why)
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
    if not U.same(rec.cur, rec.orig) then
        if not cfg_set(rec.path, rec.orig) then
            Bind.fail(sl, rec, "restore failed, original stays in the journal")
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
    Bind.clear_pub()
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
        local lists = { CUSTOM_PATHS[sl.id], PATHS_USER[sl.id] }
        for li = 1, 2 do
            local list = lists[li]
            if type(list) == "table" then
                for j = 1, #list do
                    if type(list[j]) == "string" then
                        sl.custom = true
                        Bind.add_path(sl, list[j], true)
                    end
                end
            end
        end
    end
    RB.eval_at = 0
    local ok, keys = pcall(config.keys)
    if not ok or type(keys) ~= "table" then
        say("config.keys unavailable: " .. tostring(keys) .. ". Set manual paths (CUSTOM_PATHS or a snapshot).")
        return false
    end
    for i = 1, #keys do
        local path = keys[i]
        if type(path) == "string" and not CLAIMED[path] then
            local low = s_lower(path)
            local excluded = nil
            for j = 1, #ORDER_P do
                local sl = SL[ORDER_P[j]]
                if not sl.custom and U.any_match(low, sl.patterns) then
                    if excluded == nil then excluded = U.any_match(low, GENERIC_EXCLUDE) end
                    if excluded then break end
                    if not U.any_match(low, sl.exclude) then
                        if sl.n < K.MAX_CANDS then
                            if Bind.add_path(sl, path, false) then break end
                        elseif not sl.full then
                            sl.full = true
                            say(format("%s: more than %d paths found, extras skipped. Use manual paths.", sl.title, K.MAX_CANDS))
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
            Bind.fail(sl, rec, "path no longer readable")
            return false
        end
        local pending = Journal.data[rec.path]
        if pending ~= nil and type(pending) == type(cur) then
            rec.orig = U.copy(pending)            -- previous restore failed: the real original is in the journal
        else
            rec.orig = U.copy(cur)
            Journal.add(rec.path, rec.orig)
        end
        rec.cur, rec.want, rec.eff = U.copy(cur), nil, false
        RB.touched = true
    end

    local val, supported = target, true
    if target == TRANSFORM or target == Bind.HEAD then
        local fn = (target == Bind.HEAD) and sl.head_only or sl.transform
        val = fn and fn(rec.orig) or nil
        if val == nil then
            if not rec.warned then
                rec.warned = true
                say("value format not supported, path skipped: " .. rec.path .. " = " .. fmt_v(rec.orig))
            end
            val, supported = rec.orig, false
        end
    end
    if rec.want ~= nil and U.same(rec.want, val) then return rec.eff end

    local eff
    if U.same(val, rec.orig) then
        if not U.same(rec.cur, rec.orig) then
            if not cfg_set(rec.path, rec.orig) then
                Bind.fail(sl, rec, "write rejected")
                return false
            end
            if CFG.log_cfg then say(format("%s <- %s (equals yours)", rec.path, fmt_v(rec.orig))) end
            rec.cur = U.copy(rec.orig)
        end
        eff = supported
    elseif cfg_set(rec.path, val) then
        local echo = cfg_get(rec.path)             -- config may clamp or round the value
        if echo == nil then echo = val end
        rec.cur, rec.bad = U.copy(echo), 0
        eff = not U.same(echo, rec.orig)
        if not eff and not rec.ro then
            rec.ro = true
            say("write accepted but the value did not change: " .. rec.path .. " (wanted " .. fmt_v(val) .. ")")
        end
        if CFG.log_cfg then say(format("%s: %s -> %s", rec.path, fmt_v(rec.orig), fmt_v(echo))) end
    else
        Bind.fail(sl, rec, "write rejected")
        return false
    end
    rec.want, rec.eff = U.copy(val), eff
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
                    if U.same(cur, rec.cur) then
                        rec.mism = 0
                    else
                        if not STATE.menu_open then rec.mism = rec.mism + 1 end
                        if rec.mism > K.MISM_LIMIT then
                            rec.dead = true
                            rec.orig, rec.cur, rec.want, rec.eff = NONE, nil, nil, false
                            Journal.remove(rec.path)
                            say("path disabled until rescan (constantly changed by other code): " .. rec.path)
                        else
                            rec.orig, rec.cur, rec.want, rec.eff = U.copy(cur), U.copy(cur), nil, false
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
local CAND = { list = {}, n = 0 }

function RB.reset()
    HB.cache, HB.n = {}, 0
    for i = 1, CAND.n do CAND.list[i].pawn = nil end
    CAND.n = 0
    RB.waddr, RB.wgroup, RB.state = nil, nil, nil
    RB.clear_target()
    RB.baim_reason, RB.baim_until = nil, 0
    RB.hs_reason, RB.hs_until = nil, 0
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
    if def and WPN.BY_DEF[def] then return WPN.BY_DEF[def] end
    if def and WPN.NON_GUN_DEF[def] then return nil end
    local name = type(info.name) == "string" and s_lower(info.name) or ""
    for i = 1, #WPN.BY_NAME do
        if s_find(name, WPN.BY_NAME[i][1], 1, true) then return WPN.BY_NAME[i][2] end
    end
    if WPN.non_gun_name(name) then return nil end
    return 6
end

function RB.weapon(lp)
    local w = safe(lp.weapon, lp)
    if not w then
        if RB.wgroup ~= nil then RB.eval_at, VIS.dirty = 0, true end
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

-- Landing prediction: will we touch the ground within land_ticks ticks? (createmove only)
function RB.predict()
    local ok, sim = pcall(engine.simulate, CFG.land_ticks)
    if not ok or type(sim) ~= "table" then
        RB.sim_fail = RB.sim_fail + 1
        if RB.sim_fail >= 3 and not RB.sim_disabled then
            RB.sim_disabled = true
            notify("engine.simulate unavailable: landing prediction falls back to 'Ground + vertical speed'")
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

-- Local movement state. Runs every createmove (shot bookkeeping needs it even when the
-- assist is off); the landing simulation only runs when the assist uses it.
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
    if mode == 3 and RB.sim_disabled then mode = 1 end
    local air = false
    if not grounded then
        if mode == 2 then
            air = true
        else
            air = RB.air_ticks >= 2 and (abs(vz) >= CFG.air_thr or RB.air_ticks >= 10)
        end
    end
    if air and mode == 3 and CFG.rb_enable then
        -- While rising, landing within land_ticks is impossible and the simulation is skipped.
        if not RB.land_soon and vz <= RB.g_tick * CFG.land_ticks + K.SIM_MARGIN then RB.predict() end
        if RB.land_soon then air = false end
    end
    local st
    if air then
        st = (CFG.apex_on and abs(vz) <= CFG.apex_win) and ST.APEX or ST.AIR
    elseif band(safe(lp.flags, lp) or 0, K.FL_DUCKING) ~= 0 then
        st = ST.DUCK
    elseif speed < K.MOVE_EPS then
        st = ST.STAND
    elseif cmd:has(K.BTN_SPEED) then
        st = ST.SLOW
    else
        st = ST.MOVE
    end
    STATE.lp_air = not grounded
    STATE.lp_moving = speed >= K.MOVE_EPS
    RB.mstate = st
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
    local pos = safe(pawn.hitbox, pawn, entry.index)
    if not pos then return 0 end
    local ok, d = pcall(trace.damage, pawn, pos, entry.group, eye)
    if ok and type(d) == "number" then return d end
    return 0
end

function RB.set_pub(k, v)
    if RB[k] ~= v then
        RB[k] = v
        VIS.dirty = true
    end
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
    if UI.rb_status and not is_dummy(UI.rb_status) then pcall(UI.rb_status.set, UI.rb_status, "Paths: " .. txt) end
end

function ACT.rescan()
    local ok = Bind.scan()
    local txt = ok and Bind.summary() or "config.keys unavailable"
    RB.set_status(txt)
    notify("Found: " .. txt)
end

function ACT.dump() Bind.dump() end

-- Per-tick entry point (createmove). lp is alive when given.
function RB.tick(cmd, lp)
    RB.cm_t = STATE.rt
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

    if not lp then
        if RB.state ~= nil or RB.wgroup ~= nil then RB.reset() end
        RB.stand_down(false)
        return
    end

    RB.weapon(lp)
    local grp = RB.wgroup
    if not grp or not multi_on(CFG.weapons, grp, WPN.ITEMS) then
        RB.stand_down(false)
        return
    end

    if RB.mstate ~= RB.state then
        RB.state = RB.mstate
        VIS.dirty = true
    end
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
        if IO.save() then SET.dirty = false else SET.dirty_t = now + K.IO_RETRY end
    end
    Journal.flush(false)
    if RES.store_dirty and now - RB.store_t > 30 then        -- crash safety for learned sides
        RB.store_t = now
        RES.store_save(false)
    end
    ESPX.sync()
    if STATE.strikes > 0 and now - STATE.strike_t > K.ERR_FORGIVE then STATE.strikes = 0 end
end

-- Background tasks run from paint; createmove takes over if paint goes silent.
function RB.background(now)
    cfg_tick(false)
    -- menu_toggled can be missed: cross-check with input.menu_open after a short grace period
    if now - STATE.menu_evt_t > 0.25 and now - STATE.menu_poll_t > 0.25 then
        STATE.menu_poll_t = now
        local ok, open = pcall(input.menu_open)
        if ok and type(open) == "boolean" and open ~= STATE.menu_open then
            RB.on_menu_toggled(open, true)
        end
    end
    if Journal.add_dirty then Journal.flush(false) end
    if now - RB.hk_t >= K.HK_INTERVAL then RB.housekeeping(now) end
end

function RB.on_menu_toggled(open, polled)
    STATE.menu_open = open and true or false
    if not polled then STATE.menu_evt_t = STATE.rt end
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
--  RAGE ASSIST · 4.2: target evaluation, headshot assist, decision
-- ============================================================================
RB.hs_reason, RB.hs_until, RB.head = nil, 0, nil
RB.t_bd, RB.t_hd, RB.t_state, RB.t_trust = 0, 0, 1, 0
K.T_WALK_SQR = 19600          -- target "running" above 140 u/s (squared), headshot assist states

-- Keeps only the head entries of a hitbox multi-select value. Returns the new value, the
-- original (already head-only) or nil (unsupported format / the user has no head enabled).
function RB.keep_head(v)
    if type(v) ~= "table" then return nil end
    local out, heads, others = {}, 0, 0
    if #v > 0 then
        for i = 1, #v do
            local x = v[i]
            if type(x) ~= "string" then return nil end
            if is_head_name(x) then
                out[#out + 1] = x
                heads = heads + 1
            else
                others = others + 1
            end
        end
    else
        for k, x in pairs(v) do
            if type(k) ~= "string" then return nil end
            if is_head_name(k) then
                out[k] = x
                if x then heads = heads + 1 end
            else
                out[k] = false
                if x then others = others + 1 end
            end
        end
    end
    if heads == 0 then return nil end
    if others == 0 then return v end
    return out
end
SL.hitbox.head_only = RB.keep_head

function Bind.clear_pub()
    if RB.hc ~= nil or RB.dmg ~= nil or RB.safe or RB.baim ~= nil or RB.head ~= nil or RB.strict or RB.pub_thp ~= nil then
        RB.hc, RB.dmg, RB.safe, RB.baim, RB.head, RB.strict, RB.pub_thp = nil, nil, false, nil, nil, false, nil
        VIS.dirty = true
    end
end

function RB.clear_target()
    RB.t_hp, RB.t_air, RB.t_move = nil, false, false
    RB.t_bd, RB.t_hd, RB.t_state, RB.t_trust = 0, 0, 1, 0
    if RB.t_addr ~= nil then RB.t_addr, RB.baim_until, RB.hs_until = nil, 0, 0 end
end

-- Headshot assist: is the head the right target for the picked candidate? Returns a reason
-- tag or nil. Needs resolver data for the target; every "do not trust" case returns nil.
function RB.head_reason(c)
    local rec = RES.by_pawn[RB.t_addr]
    if not rec or RES.unresolved(rec) then
        RB.t_trust = 0
        return nil
    end
    local trust = RES.trust(rec)
    RB.t_trust = trust
    if trust * 100 < CFG.hs_trust then return nil end
    if RB.t_air or STATE.lp_air then return nil end
    if not multi_on(CFG.hs_states, RB.t_state, ITEMS.HS_STATES) then return nil end
    local hd, bd, hp = c.hd, c.bd, c.hp
    if hd <= 0 then return nil end                               -- head not hittable from here
    if CFG.hs_body_first and bd >= hp then return nil end        -- one body shot already kills
    local need = CFG.hs_need
    if need == 1 then
        return (hd >= hp) and "LETHAL" or nil
    elseif need == 2 then
        if hd >= hp then return "LETHAL" end
        return (hd > bd * 1.25) and "DMG" or nil
    end
    return "TRUST"
end

function RB.eval_targets(lp)
    local grp = RB.wgroup
    RB.base_hc = Bind.base(SL.hc, grp)
    RB.base_dmg = Bind.base(SL.dmg, grp)

    local baim_ok = CFG.baim_on and (SL.baim.n + SL.hitbox.n) > 0
    local hs_ok = CFG.hs_on and CFG.enable and (SL.hitbox.n > 0 or (CFG.hs_gate and SL.dmg.n > 0))
    local need_trace = hs_ok or (baim_ok and (CFG.baim_lethal or CFG.baim_2x))
    local need_target = need_trace or (baim_ok and (CFG.baim_hp_on or CFG.baim_unres))
        or (CFG.dmg_cap and SL.dmg.n > 0)
        or ((CFG.hc_tgt_air ~= 0 or CFG.hc_tgt_move ~= 0 or CFG.unres_hc ~= 0) and SL.hc.n > 0)
    local eye, view = nil, nil
    if need_target then eye, view = safe(lp.eye_position, lp), safe(engine.view_angles) end
    if not eye or not view then
        RB.clear_target()
        RB.baim_reason, RB.hs_reason = nil, nil
        return
    end

    local aim_from = vector(eye.x, eye.y, eye.z - K.EYE_OFFSET)   -- compare against target origin
    local lim = CFG.baim_fov
    local players = safe(entity.players)
    local list, n = CAND.list, 0
    if type(players) == "table" then
        for i = 1, #players do
            local p = players[i]
            local pawn = type(p) == "table" and p.pawn or nil
            if pawn and pawn:alive() and pawn:is_enemy() then
                local o = pawn:origin()
                if o then
                    local fov = U.fov(aim_from, o, view)
                    if fov <= lim then
                        n = n + 1
                        local c = list[n]
                        if not c then
                            c = {}
                            list[n] = c
                        end
                        c.pawn, c.fov, c.hp, c.bd, c.hd = pawn, fov, 100, 0, 0
                    end
                end
            end
        end
    end
    for i = n + 1, CAND.n do list[i].pawn = nil end
    CAND.n = n

    -- Partial selection sort: only the MAX_TARGETS closest are traced.
    local pick = nil
    for i = 1, min(n, K.MAX_TARGETS) do
        local m = i
        for j = i + 1, n do
            if list[j].fov < list[m].fov then m = j end
        end
        if m ~= i then list[i], list[m] = list[m], list[i] end
        local c = list[i]
        c.hp = safe(c.pawn.health, c.pawn) or 100
        if need_trace then
            local ids = RB.hitbox_ids(c.pawn)
            if ids then
                local need = c.hp + CFG.baim_margin
                for j = 1, #ids.body do
                    local d = RB.dmg_at(eye, c.pawn, ids.body[j])
                    if d > c.bd then c.bd = d end
                    if d >= need and not hs_ok then break end      -- the assist wants the real maximum
                end
                if ids.head and (hs_ok or (CFG.baim_2x and c.bd > 0 and c.bd * 2 >= need
                    and not (CFG.baim_lethal and c.bd >= need))) then
                    c.hd = RB.dmg_at(eye, c.pawn, ids.head)
                end
            end
        end
        if not pick then pick = c end
        if c.bd > 0 or c.hd > 0 then
            pick = c
            break
        end
    end

    local reason, hs = nil, nil
    if pick then
        local p = pick.pawn
        local addr = p:address()
        if addr ~= RB.t_addr then RB.t_addr, RB.baim_until, RB.hs_until = addr, 0, 0 end
        RB.t_hp, RB.t_bd, RB.t_hd = pick.hp, pick.bd, pick.hd
        RB.t_air = (safe(p.on_ground, p) == false)
        local pv = safe(p.velocity, p)
        local sp2 = pv and (pv.x * pv.x + pv.y * pv.y) or 0
        RB.t_move = sp2 > K.T_MOVE_SQR
        if band(safe(p.flags, p) or 0, K.FL_DUCKING) ~= 0 then RB.t_state = 2
        elseif sp2 < 25 then RB.t_state = 1
        elseif sp2 < K.T_WALK_SQR then RB.t_state = 3
        else RB.t_state = 4 end
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
        if hs_ok and not reason then hs = RB.head_reason(pick) end
    else
        RB.clear_target()
    end

    if reason then
        RB.baim_reason, RB.baim_until = reason, RB.tick_n + K.HOLD_TICKS
    elseif RB.tick_n > RB.baim_until then
        RB.baim_reason = nil
    end
    if hs then
        RB.hs_reason, RB.hs_until = hs, RB.tick_n + K.HOLD_TICKS
    elseif reason or RB.tick_n > RB.hs_until then
        RB.hs_reason = nil
    end
end

function RB.decide(grp)
    local st = RB.state
    local airborne = (st == ST.AIR or st == ST.APEX)
    local strict, kbaim, kdmg, khead = bind_on(UI.k_strict), bind_on(UI.k_baim), bind_on(UI.k_dmg), bind_on(UI.k_head)
    if not CFG.baim_on then RB.baim_reason = nil end
    if not (CFG.hs_on and CFG.enable) then RB.hs_reason = nil end

    -- resolver synergy: how much do we trust the guess for the crosshair target?
    local trec = RB.t_addr and RES.by_pawn[RB.t_addr] or nil
    local unres = (trec ~= nil) and CFG.enable and RES.unresolved(trec) or false
    RB.t_unres = unres

    -- body or head? Keys first, then lethal body, then the headshot assist, then "unresolved".
    local baim, head = nil, nil
    if kbaim then
        baim = "KEY"
    elseif khead then
        head = "KEY"
    elseif RB.baim_reason then
        baim = RB.baim_reason
    elseif RB.hs_reason and not unres then
        head = RB.hs_reason
    elseif unres and CFG.baim_on and CFG.baim_unres then
        baim = unres
    end

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
    if head and CFG.hs_hc > 0 then
        if not hc then hc = RB.base_hc end
        if hc then hc = hc + CFG.hs_hc end
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
    local gated = false
    if head and CFG.hs_gate and not kdmg and RB.t_hp and RB.t_hd > 0 then
        -- just above the best body damage, never above what the head deals or the target's HP
        local gate = min(floor(RB.t_bd) + 1, floor(RB.t_hd), RB.t_hp)
        if gate >= 1 and gate > (dmg or RB.base_dmg or 0) then dmg, gated = gate, true end
    end
    if CFG.dmg_cap and RB.t_hp then
        local base = dmg or RB.base_dmg
        if base and base <= 100 and RB.t_hp < base then dmg = max(1, RB.t_hp) end
    end
    if dmg then dmg = clamp(round(dmg), 1, 130) end

    -- safepoint, body-aim flag, hitbox list
    local want_safe_b = (airborne and CFG.air_on and CFG.air_safe) or strict
    local want_safe = want_safe_b and TRANSFORM or nil
    local want_baim = baim and TRANSFORM or nil
    Bind.apply(SL.hc, hc, grp)
    Bind.apply(SL.dmg, dmg, grp)
    Bind.apply(SL.safe, want_safe, grp)
    Bind.apply(SL.baim, want_baim, grp)
    Bind.apply(SL.hitbox, want_baim or (head and Bind.HEAD) or nil, grp)

    -- the panel shows only what is really written into the ragebot
    local hc_live, safe_live, dmg_live = SL.hc.live > 0, SL.safe.live > 0, SL.dmg.live > 0
    RB.set_pub("hc", hc_live and hc or nil)
    RB.set_pub("dmg", dmg_live and dmg or nil)
    RB.set_pub("safe", (want_safe_b and safe_live) and true or false)
    RB.set_pub("baim", (baim and SL.baim.live + SL.hitbox.live > 0) and baim or nil)
    RB.set_pub("head", (head and (SL.hitbox.live > 0 or (gated and dmg_live))) and head or nil)
    RB.set_pub("strict", (strict and (hc_live or safe_live)) and true or false)
    RB.set_pub("pub_thp", RB.t_hp)
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

VIS.IND_KEYS = { "SELF", "MODE", "HC", "DMG", "SAFE", "BAIM", "STRICT", "TARGET", "AA", "YAW", "CONF", "PITCH", "HITS", "LC", "HEAD", "TRUST" }
VIS.IND_VALS = { "PAUSE", "100%", "130", "ON", "LETHAL", "100 HP", "JITTER L*", "+180°", "FLICK", "99/99", "BREAK", "FREESTAND", "STANDING" }

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
    return U.utf8_len(str) * size * 0.55, size
end

function VIS.text_w(str)
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
function VIS.side_label(rec) return ((rec.pred_side > 0) and "L" or "R") .. (rec.manual and "*" or "") end

function VIS.live(rec, rt) return rec.pawn and rec.resolved and rt - rec.seen_rt < 0.1 end

function VIS.overlay(rt, P)
    local detailed = (CFG.ov_style == 2)
    local focus = RES.focus
    for _, rec in pairs(RES.records) do
        if VIS.live(rec, rt) then
            local ok, l, t, r = pcall(rec.pawn.bbox, rec.pawn)
            if ok and type(l) == "number" and type(t) == "number" and type(r) == "number" then
                local col = rec.lc and P.warn or (rec.applied and P.val or P.key)
                local dlt = normalize(rec.resolved_yaw - rec.raw_yaw)
                local txt = format("%s %s %d°%s", MODE_LABEL[rec.mode] or "?", VIS.side_label(rec), round(abs(dlt)), rec.lc and " LC" or "")
                local w = render.text_size(txt) or 0
                local cx = (l + r) * 0.5
                local y = t - (detailed and 30 or 16)
                render.text(cx - w * 0.5, y, col, txt)
                if detailed then
                    local sub = format("%d/%d · b%d%s%s", rec.hits, rec.misses, rec.brute_idx,
                        rec.pitch_kind ~= "" and (" · " .. rec.pitch_kind) or "",
                        rec.last_reason and (" · " .. rec.last_reason) or "")
                    local sw = render.text_size(sub) or 0
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
        if VIS.live(rec, rt) then
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
    for i = 1, #VIS.IND_KEYS do kw = max(kw, VIS.text_w(VIS.IND_KEYS[i])) end
    for i = 1, #VIS.IND_VALS do vw = max(vw, VIS.text_w(VIS.IND_VALS[i])) end
    for i = 1, #ST_NAME do vw = max(vw, VIS.text_w(ST_NAME[i])) end
    local pad = floor(size * 0.8)
    local tw, th = VIS.measure("0x", size + 2)
    local vwid = VIS.measure(VIS.ver, size - 2)
    VIS.pad, VIS.rh, VIS.th, VIS.tw = pad, floor(size * 1.55), th, tw
    VIS.w = max(pad * 2 + kw + 18 + vw, pad * 2 + tw + 6 + vwid + 40, floor(size * 13))
end

function VIS.put_row(i, k, value, kind, frac)
    local r = VIS.rows[i]
    if not r then
        r = {}
        VIS.rows[i] = r
    end
    r[1], r[2], r[3], r[4], r[5] = k, value, kind, VIS.text_w(value), frac
    return i + 1
end

function VIS.rebuild(rb_show, rec)
    local put, n = VIS.put_row, 1
    if CFG.aa_on then n = put(n, "SELF", AA.label_txt, AA.active and 2 or 3) end
    if rb_show then
        n = put(n, "MODE", RB.paused and "PAUSE" or (RB.state and ST_NAME[RB.state] or "—"), 1)
        if RB.hc then n = put(n, "HC", RB.hc .. "%", 1) end
        if RB.dmg then n = put(n, "DMG", tostring(RB.dmg), 1) end
        if RB.safe then n = put(n, "SAFE", "ON", 2) end
        if RB.baim then n = put(n, "BAIM", RB.baim, 3) end
        if RB.head then n = put(n, "HEAD", RB.head, 2) end
        if RB.strict then n = put(n, "STRICT", "ON", 2) end
        if RB.pub_thp then n = put(n, "TARGET", RB.pub_thp .. " HP", 1) end
    end
    if rec then
        n = put(n, "AA", (MODE_LABEL[rec.mode] or "?") .. " " .. VIS.side_label(rec), rec.applied and 2 or 1)
        n = put(n, "YAW", format("%+d°", round(normalize(rec.resolved_yaw - rec.raw_yaw))), 1)
        if rec.pitch_kind ~= "" then n = put(n, "PITCH", rec.pitch_kind, 3) end
        if rec.lc then n = put(n, "LC", "BREAK", 3) end
        n = put(n, "CONF", format("%d%%", round(rec.conf * 100)), 4, rec.conf)
        n = put(n, "TRUST", format("%d%%", round(RES.trust(rec) * 100)), 1)
        n = put(n, "HITS", format("%d/%d", rec.hits, rec.misses), 1)
    end
    VIS.nrows = n - 1
    VIS.h = VIS.pad * 2 + VIS.th + 8 + VIS.nrows * VIS.rh + ((rb_show and RB.hc) and 8 or 0)
end

function VIS.commit_drag(w, h)
    local nx = clamp(round(VIS.px / max(1, STATE.sw - w) * 100), 0, 100)
    local ny = clamp(round(VIS.py / max(1, STATE.sh - h) * 100), 0, 100)
    if REG.panel_x then write_el(REG.panel_x, nx) end
    if REG.panel_y then write_el(REG.panel_y, ny) end
    CFG.panel_x, CFG.panel_y = nx, ny
    VIS.drag, VIS.px, VIS.py = nil, nil, nil
    SET.dirty, SET.dirty_t = true, STATE.rt
end

-- true when the cursor is over the Neverlose menu window (clicks there belong to the menu).
function VIS.over_menu(mx, my)
    local p, s = safe(ui.position), safe(ui.size)
    if type(p) ~= "table" or type(s) ~= "table" or type(p.x) ~= "number" or type(s.x) ~= "number" then return false end
    return mx >= p.x and mx <= p.x + s.x and my >= p.y and my <= p.y + s.y
end

-- Panel position; draggable with the left mouse button while the menu is open.
function VIS.position(w, h)
    local x = floor((STATE.sw - w) * CFG.panel_x / 100)
    local y = floor((STATE.sh - h) * CFG.panel_y / 100)
    if STATE.menu_open then
        local ok, mx, my = pcall(input.cursor)
        local down = safe(input.key_down, K.VK_LBUTTON) == true
        if ok and type(mx) == "number" and type(my) == "number" then
            if VIS.drag then
                if down then
                    VIS.px = clamp(mx - VIS.drag.dx, 0, max(0, STATE.sw - w))
                    VIS.py = clamp(my - VIS.drag.dy, 0, max(0, STATE.sh - h))
                else
                    VIS.commit_drag(w, h)
                end
            elseif down and not VIS.was_down and mx >= x and mx <= x + w and my >= y and my <= y + h
                and not VIS.over_menu(mx, my) then
                VIS.drag = { dx = mx - x, dy = my - y }
                VIS.px, VIS.py = x, y
            end
        end
        VIS.was_down = down
    else
        if VIS.drag then VIS.commit_drag(w, h) end
        VIS.was_down = false
    end
    if VIS.px then return VIS.px, VIS.py end
    return x, y
end

function VIS.panel(rt)
    local rb_show = CFG.rb_enable and (RB.state ~= nil or RB.paused)
    local rec = CFG.enable and RES.focus or nil
    if rec and (not rec.resolved or rt - rec.seen_rt > 0.5) then rec = nil end
    local show = (rb_show or rec ~= nil or (CFG.aa_on and AA.why ~= "OFF" and AA.why ~= "DEAD")) and RB.in_game
    local a = VIS.a
    if not show and a == 0 then return end
    a = a + ((show and 1 or 0) - a) * min(1, (safe(globals.frametime) or 0.016) * 10)
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
    render.rect_filled(x + 1, y + 10, 2, max(1, h - 20), P.acc, 1)
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
        local a = clamp(C.FEED_LIFE - (rt - e.t), 0, 1)
        local col = P.val
        if e.kind == "hit" then col = P.good
        elseif e.kind == "miss" then col = P.warn
        elseif e.kind == "kill" then col = P.acc
        elseif e.kind == "info" then col = P.key end
        VIS.text(x + 2, y, (a < 1) and col:alpha(floor(col.a * a)) or col, e.text, size)
        y = y + size + 4
    end
end

-- ---------------------------------------------------------------- debug
function VIS.debug(rt, P)
    local x, y = 24, 120
    local rows = {}
    local s = RES.stats
    rows[#rows + 1] = format("%s v%s  insecure=%s write=%s simtime=%s body=%s pending=%d focus=%s",
        META.name, META.version, tostring(RES.insecure), tostring(RES.write_ok), tostring(RES.simtime_ok),
        tostring(RES.body_ok), #RES.pending, RES.focus and tostring(RES.focus.name) or "-")
    rows[#rows + 1] = format("ragebot: on=%s state=%s grp=%s hc=%s dmg=%s safe=%s baim=%s unres=%s paths=%s touched=%s sim=%s",
        tostring(CFG.rb_enable), RB.state and ST_NAME[RB.state] or "-", tostring(RB.wgroup), tostring(RB.hc),
        tostring(RB.dmg), tostring(RB.safe), tostring(RB.baim), tostring(RB.t_unres), Bind.summary(), tostring(RB.touched),
        RB.sim_disabled and "off" or "on")
    rows[#rows + 1] = format("shots=%d hits=%d heads=%d misses=%d  [resolver %d · spread %d · lagcomp %d · moving %d · air %d]",
        s.shots, s.hits, s.heads, s.misses, s.resolver, s.spread, s.lagcomp, s.moving, s.airborne)
    local hw = RES.hw
    rows[#rows + 1] = format("hint weights: body %.2f · freestand %.2f · move %.2f · movedir %.2f   misses: death %d · lost %d",
        hw.b, hw.fs, hw.mv, hw.md, s.death, s.lost)
    local pt = {}
    for name, ms in pairs(STATE.prof) do pt[#pt + 1] = format("%s %.3f", name, ms) end
    tsort(pt)
    rows[#rows + 1] = "callback ms: " .. tconcat(pt, " · ")
    for _, rec in pairs(RES.records) do
        if rt - rec.seen_rt < 1 then
            local m = RES.brute_entry(rec)
            rows[#rows + 1] = format(
                "%-14s %-6s side=%s conf=%.2f score=%+.2f brute=%d(%+.2f) body=%+d fs=%+d mv=%+.1f md=%+d ab=%d amt=%d res=%d raw=%d p=%s h/m=%d/%d%s%s",
                s_sub(tostring(rec.name), 1, 14), MODE_LABEL[rec.mode] or "?", VIS.side_label(rec), rec.conf, rec.score,
                rec.brute_idx, m, round(rec.body_delta), rec.fs_hint, rec.mv_hint, rec.md_hint, rec.ab_score,
                round(rec.amount), round(rec.resolved_yaw), round(rec.raw_yaw), rec.pitch_kind ~= "" and rec.pitch_kind or "-",
                rec.hits, rec.misses, rec.lc and " [LC]" or "", rec.applied and "" or " [track]")
            if rec.mode == "jitter" then
                rows[#rows + 1] = format("   jitter: half=%d period=%d run=%d conf=%.2f k=%s", round(rec.jit_half), rec.jit_period,
                    rec.jit_run, rec.jit_pconf, rec.jit_k and format("%+.1f", rec.jit_k) or "legacy")
            end
        end
    end
    local wmax = 0
    for i = 1, #rows do
        local w = render.text_size(rows[i]) or 0
        if w > wmax then wmax = w end
    end
    render.rect_filled(x - 8, y - 6, wmax + 16, #rows * 15 + 12, color(12, 12, 14, 200), 4)
    for i = 1, #rows do
        render.text(x, y + (i - 1) * 15, i <= 5 and P.acc or P.key, rows[i])
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
    local s = RES.stats
    if UI.stats and not is_dummy(UI.stats) then
        pcall(UI.stats.set, UI.stats, format("tracked %d · hits %d (%d hs) · misses %d (res %d · spread %d · lc %d) · write %s",
            tracked, s.hits, s.heads, s.misses, s.resolver, s.spread, s.lagcomp,
            RES.write_ok == true and "on" or (RES.write_ok == false and "off" or "n/a")))
    end
end

function VIS.paint()
    local rt = STATE.rt
    VIS.stats(rt)
    if not CFG.enable and not CFG.rb_enable and not CFG.aa_on then
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
    if CFG.aa_on and RB.in_game then AA.arrows(P) end
    if CFG.debug and CFG.enable then VIS.debug(rt, P) end
end

-- ============================================================================
--  NATIVE ESP FLAG (esp.add_text) — created only while the option is on
-- ============================================================================
ESPX.name, ESPX.el = "0x resolver", nil

function ESPX.text(ent)
    if not ent or not CFG.enable or not CFG.esp_flag then return nil end
    local rec = RES.record_by_pawn(ent)
    if not rec then
        local p = safe(ent.pawn, ent)                 -- the element may receive a controller
        rec = p and RES.record_by_pawn(p) or nil
    end
    if not rec or not rec.resolved or (safe(globals.realtime) or 0) - rec.seen_rt > 0.5 then return nil end
    return format("%s %s%s", MODE_LABEL[rec.mode] or "?", VIS.side_label(rec), rec.lc and " LC" or "")
end

function ESPX.sync()
    local want = CFG.enable and CFG.esp_flag
    if want and not ESPX.el then
        if type(esp) ~= "table" or type(esp.add_text) ~= "function" then return end
        local ok, el = pcall(esp.add_text, ESPX.name, function(ent)
            if STATE.failed then return nil end
            local ok2, v = pcall(ESPX.text, ent)
            if ok2 then return v end
            return nil
        end, { side = "right", small = true })
        if ok and el then
            ESPX.el = el
        else
            say("native ESP flag unavailable: " .. tostring(el))
            CFG.esp_flag = false
            if REG.esp_flag then write_el(REG.esp_flag, false) end
        end
    elseif not want and ESPX.el then
        ESPX.remove()
    end
end

function ESPX.remove()
    if not ESPX.el then return end
    if not pcall(esp.remove, ESPX.name) then pcall(ESPX.el.remove, ESPX.el) end
    ESPX.el = nil
end

-- ============================================================================
--  ANTI-AIM
--  There is no anti-aim module in the API: the angles are written into the command
--  (cmd:set_view_angles) in createmove and the movement is kept camera-relative.
--  4.2: 8 conditions with fallbacks, asymmetric jitter (left / right add), random switch
--  delay, range randomization, Skitter / Flick modifiers, pitch jitter / sway / random,
--  anti-bruteforce on enemy misses, edge yaw, safe head and full presets.
-- ============================================================================

-- Private Park-Miller generators: anti-aim and Tetris never touch math.random (and each other).
function U.rng(seed)
    local s = floor(tonumber(seed) or 1) % 2147483646 + 1
    return function()
        s = (s * 16807) % 2147483647
        return s / 2147483647
    end
end

K.AA_EDGE_DIST, K.AA_AB_FOV, K.AA_AB_WAIT, K.AA_SAFE_Z = 30, 10, 0.25, 64

AA.t, AA.active, AA.why, AA.src, AA.label_txt = 0, false, "OFF", "BUILDER", "OFF"
AA.manual, AA.key_prev, AA.edit_shown = nil, {}, nil
AA.at_yaw, AA.knife_yaw, AA.t_eye, AA.edge_yaw, AA.scan_t, AA.fs_side = nil, nil, nil, nil, -1e9, 0
AA.hurt_until, AA.hurt_sign = -1e9, 1
AA.phase, AA.hold_left, AA.cond, AA.rand, AA.rand2, AA.rand3 = 0, 0, 1, 0.5, 0.5, 0.5
AA.ab_n, AA.ab_until, AA.ab_pending = 0, -1e9, nil
AA.fails, AA.dead, AA.rot_ok = 0, false, true
AA.rng = U.rng(os.time())
AA.fs_opts = { mask = E.MASK_VISIBLE }
AA.STATE_OF = { [ST.STAND] = 2, [ST.SLOW] = 3, [ST.MOVE] = 4, [ST.DUCK] = 5, [ST.AIR] = 6, [ST.APEX] = 6 }
AA.FALLBACK = { [7] = 5, [8] = 6 }                       -- Duck-moving -> Ducking, Air-duck -> Air, then Shared
AA.FIELDS = { "on", "pitch", "pitch_v", "base", "yaw", "yaw_l", "yaw_r", "mod", "range", "rnd", "delay", "delay_max", "speed" }
AA.DEFAULTS = { on = false, pitch = 2, pitch_v = 89, base = 2, yaw = 180, yaw_l = 0, yaw_r = 0, mod = 1,
                range = 60, rnd = 0, delay = 1, delay_max = 1, speed = 20 }
AA.MANUAL = { { "k_aa_left", 90, "LEFT" }, { "k_aa_right", -90, "RIGHT" }, { "k_aa_back", 180, "BACK" }, { "k_aa_fwd", 0, "FWD" } }
AA.SEQ3, AA.SEQ5, AA.SKIT, AA.AB_SEQ = { -1, 0, 1 }, { -1, -0.5, 0, 0.5, 1 }, { -1, 1, 0, 1, -1, 0 }, { 1, -1, 2, -2 }
AA.KEYS = {}
for i = 1, #ITEMS.AA_STATE do
    local t = {}
    for j = 1, #AA.FIELDS do t[AA.FIELDS[j]] = "aa" .. i .. "_" .. AA.FIELDS[j] end
    AA.KEYS[i] = t
end

-- Full presets: s = per-condition values (missing fields = defaults, missing conditions = override
-- off), g = other menu ids. Order matches ITEMS.AA_PRESET.
AA.PRESETS = {
    { s = { [1] = { mod = 2, range = 60 } } },
    { s = { [1] = {} } },
    { s = { [1] = { base = 1, yaw = 0, mod = 6, speed = 30 } } },
    { s = { [1] = { mod = 2, range = 84, delay = 3, delay_max = 6 } } },
    { s = { [1] = { mod = 5, range = 100 } } },
    { s = { [1] = { mod = 7, range = 36, speed = 9 } } },
    { s = { [1] = { mod = 9, range = 70, rnd = 40, delay_max = 3 } } },
    { s = { [1] = { mod = 2, range = 60 },
            [2] = { on = true, mod = 2, range = 52, delay = 2, delay_max = 4, yaw_l = 6, yaw_r = -6 },
            [3] = { on = true, mod = 4, range = 70 },
            [4] = { on = true, mod = 2, range = 74 },
            [5] = { on = true, mod = 2, range = 40, delay = 3, delay_max = 5 },
            [6] = { on = true, mod = 9, range = 80, rnd = 30 },
            [7] = { on = true, mod = 5, range = 60 },
            [8] = { on = true, mod = 2, range = 60, delay = 2, delay_max = 3 } },
      g = { aa_ab = 4, aa_hurt = true, aa_knife = true } },
    { s = { [1] = { mod = 8, range = 140, delay_max = 2 } } },
    { s = { [1] = { mod = 7, range = 14, speed = 6 } }, g = { aa_ab = 1 } },
}

-- Only the widgets of the condition selected in "Edit condition" are shown.
function AA.sync_menu()
    local edit = CFG.aa_edit or 1
    if edit == AA.edit_shown then return end
    AA.edit_shown = edit
    for i = 1, #AA.KEYS do
        for j = 1, #AA.FIELDS do
            local r = REG[AA.KEYS[i][AA.FIELDS[j]]]
            if r and not is_dummy(r.el) then pcall(r.el.visible, r.el, i == edit) end
        end
    end
end

function AA.set_label(txt)
    if AA.label_txt ~= txt then
        AA.label_txt = txt
        VIS.dirty = true
    end
end

function AA.idle(why)
    AA.active, AA.why = false, why
    AA.set_label(why)
end

-- "gun" | "knife" | "other" (grenades, C4, ...) | "none", plus the weapon definition index.
function AA.weapon_kind(pawn)
    local info = safe(pawn.weapon_info, pawn)
    if type(info) ~= "table" then return "none", nil end
    local name = type(info.name) == "string" and s_lower(info.name) or ""
    if s_find(name, "knife", 1, true) or s_find(name, "bayonet", 1, true) then return "knife", tonumber(info.def) end
    if info.gun == false or WPN.non_gun_name(name) then return "other", tonumber(info.def) end
    return "gun", tonumber(info.def)
end

-- The most recently activated manual bind wins; releasing it falls back to another active one.
-- Frozen while Tetris owns the keyboard (its keys may be bound here).
function AA.update_manual()
    if STATE.kb_captured then return end
    local cur, prev = AA.manual, AA.key_prev
    for i = 1, #AA.MANUAL do
        local on = bind_on(UI[AA.MANUAL[i][1]])
        if on and not prev[i] then cur = i end
        prev[i] = on
    end
    if cur and not prev[cur] then
        cur = nil
        for i = 1, #AA.MANUAL do
            if prev[i] then cur = i break end
        end
    end
    AA.manual = cur
end

-- At-target enemy and the closest knife carrier (createmove only: entity reads).
function AA.scan(eye, view)
    AA.at_yaw, AA.knife_yaw, AA.t_eye = nil, nil, nil
    local players = safe(entity.players)
    if type(players) ~= "table" then return end
    local by_dist = (CFG.aa_target == 2)
    local best, best_v = nil, 1e9
    local knife_d = CFG.aa_knife and CFG.aa_knife_dist or 0
    for i = 1, #players do
        local p = players[i]
        local pawn = type(p) == "table" and p.pawn or nil
        if pawn and safe(pawn.alive, pawn) == true and safe(pawn.is_enemy, pawn) == true then
            local pe = safe(pawn.eye_position, pawn)
            if pe then
                local dist = eye:dist(pe)
                local v = by_dist and dist or U.fov(eye, pe, view)
                if v < best_v then best, best_v = pe, v end
                if dist < knife_d and AA.weapon_kind(pawn) == "knife" then
                    knife_d = dist
                    AA.knife_yaw = U.yaw_to(eye, pe)
                end
            end
        end
    end
    if best then AA.at_yaw, AA.t_eye = U.yaw_to(eye, best), best end
end

-- +1: the point left of our head is hidden from the target, -1: the right one, 0: no decision.
function AA.freestand(lp, eye)
    local te = AA.t_eye
    if not te then return 0 end
    local a = rad(U.yaw_to(eye, te))
    local lx, ly = -sin(a) * K.AA_FS_OFFSET, cos(a) * K.AA_FS_OFFSET     -- our left while facing him
    AA.fs_opts.skip = lp
    local tl = safe(trace.line, te, vector(eye.x + lx, eye.y + ly, eye.z), AA.fs_opts)
    local tr = safe(trace.line, te, vector(eye.x - lx, eye.y - ly, eye.z), AA.fs_opts)
    AA.fs_opts.skip = nil
    if type(tl) ~= "table" or type(tr) ~= "table" then return 0 end
    local bl, br = (tonumber(tl.fraction) or 1) < 0.98, (tonumber(tr.fraction) or 1) < 0.98
    if bl == br then return 0 end
    return bl and 1 or -1
end

-- Yaw toward the closest wall within AA_EDGE_DIST (8 horizontal traces), or nil.
function AA.edge(lp, eye)
    local best, best_f, d = nil, 0.999, K.AA_EDGE_DIST
    AA.fs_opts.skip = lp
    for i = 0, 7 do
        local r = rad(i * 45)
        local tr = safe(trace.line, eye, vector(eye.x + cos(r) * d, eye.y + sin(r) * d, eye.z), AA.fs_opts)
        local f = type(tr) == "table" and tonumber(tr.fraction) or 1
        if f < best_f then best, best_f = i * 45, f end
    end
    AA.fs_opts.skip = nil
    return best
end

function AA.safe_head(kind, eye)
    local v = CFG.aa_safe
    if kind == "knife" and multi_on(v, 1, ITEMS.AA_SAFE) then return true end
    local te = AA.t_eye
    return te ~= nil and eye.z - te.z > K.AA_SAFE_Z and multi_on(v, 2, ITEMS.AA_SAFE)
end

-- One step of the phase clock per tick. A phase lasts `delay` ticks, or a random number of
-- ticks between delay and delay_max.
function AA.advance(k)
    AA.hold_left = AA.hold_left - 1
    if AA.hold_left > 0 then return end
    AA.phase = AA.phase + 1
    local d1, d2 = CFG[k.delay], CFG[k.delay_max]
    AA.hold_left = (d2 > d1) and (d1 + floor(AA.rng() * (d2 - d1 + 1))) or d1
    AA.rand, AA.rand2, AA.rand3 = AA.rng(), AA.rng(), AA.rng()
end

-- Yaw modifier of a condition: degrees and the side it is on (+1 left, -1 right, 0 none).
function AA.modifier(k, shift)
    local mod = CFG[k.mod]
    if mod == 1 then return 0, 0 end
    local range, rnd = CFG[k.range], CFG[k.rnd]
    if rnd > 0 then range = range * (1 - rnd / 100 * AA.rand2) end
    local ph = AA.phase + shift
    if mod == 2 then
        local s = (ph % 2 == 0) and 1 or -1
        return s * range * 0.5, s
    elseif mod == 3 then
        if ph % 2 == 0 then return range, 1 end
        return 0, -1
    elseif mod == 4 then
        local v = AA.SEQ3[ph % 3 + 1]
        return v * range * 0.5, sign(v)
    elseif mod == 5 then
        local v = AA.SEQ5[ph % 5 + 1]
        return v * range * 0.5, sign(v)
    elseif mod == 6 then
        return (AA.t * CFG[k.speed]) % 360, 0
    elseif mod == 7 then
        return sin(rad(AA.t * CFG[k.speed])) * range * 0.5, 0
    elseif mod == 8 then
        local v = AA.rand - 0.5
        return v * range, sign(v)
    elseif mod == 9 then
        local v = AA.SKIT[ph % 6 + 1]
        return v * range * 0.5, sign(v)
    end
    -- Flick: every <speed> ticks the yaw jumps by the range for <delay> ticks
    if AA.t % max(2, CFG[k.speed]) < CFG[k.delay] then return range, 1 end
    return 0, 0
end

-- Keeps the movement relative to the camera yaw (cam) after the command yaw became yaw.
function AA.fix_movement(cmd, cam, yaw)
    local fix = CFG.aa_fix
    if fix == 3 then return end
    if fix == 1 and AA.rot_ok then
        if pcall(cmd.rotate_movement, cmd, cam) then return end
        AA.rot_ok = false
        say("cmd:rotate_movement failed; the manual movement fix is used instead")
    end
    local ok, f, sd = pcall(cmd.move, cmd)
    if not ok or type(f) ~= "number" or type(sd) ~= "number" or (f == 0 and sd == 0) then return end
    local inv = CFG.aa_fix_inv
    local l = inv and -sd or sd                               -- left-positive unless inverted
    local d = rad(normalize(yaw - cam))
    local cd, sn = cos(d), sin(d)
    local nf, nl = f * cd + l * sn, l * cd - f * sn
    pcall(cmd.set_move, cmd, nf, inv and -nl or nl)
end

-- Anti-bruteforce bookkeeping: an enemy shot at us that did not hurt within AA_AB_WAIT is a miss.
function AA.track_misses(rt)
    local p = AA.ab_pending
    if p and (rt - p > K.AA_AB_WAIT or rt < p) then
        AA.ab_pending = nil
        if CFG.aa_ab ~= 1 then
            AA.ab_n, AA.ab_until = AA.ab_n + 1, rt + CFG.aa_ab_time
            VIS.push("info", format("anti-brute: enemy missed -> variant %d", AA.ab_n))
        end
    end
    if AA.ab_n > 0 and (rt > AA.ab_until or CFG.aa_ab == 1) then AA.ab_n = 0 end
end

-- Per-tick entry point (createmove, after the rage assist). lp is alive when given.
function AA.run(cmd, lp)
    if not CFG.aa_on then return AA.idle("OFF") end
    if AA.dead then return AA.idle("ERROR") end
    if not lp then return AA.idle("DEAD") end
    local rt = STATE.rt
    AA.t = AA.t + 1
    AA.update_manual()
    AA.track_misses(rt)

    -- situations in which the real angles must reach the server
    if bind_on(UI.k_aa_off) then return AA.idle("KEY") end
    if cmd:has(K.BTN_ATTACK) then return AA.idle("SHOT") end
    local kind, def = AA.weapon_kind(lp)
    if kind == "other" or kind == "none" then return AA.idle("ITEM") end
    if cmd:has(K.BTN_ATTACK2) and (kind == "knife" or def == K.DEF_REVOLVER) then return AA.idle("SHOT") end
    if CFG.aa_use and cmd:has(K.BTN_USE) then return AA.idle("USE") end
    if CFG.aa_freeze and safe(game.freeze_time) == true then return AA.idle("FREEZE") end
    if CFG.aa_warmup and safe(game.warmup) == true then return AA.idle("WARMUP") end
    if CFG.aa_ladder then
        local ps = safe(engine.post_state)
        local mt = type(ps) == "table" and ps.move_type or nil
        if mt == K.MT_LADDER or mt == K.MT_NOCLIP then return AA.idle("LADDER") end
    end

    local view, eye = safe(cmd.view_angles, cmd), safe(lp.eye_position, lp)
    if not view or not eye then return AA.idle("N/A") end
    local cam = view.y
    local air = STATE.lp_air
    local duck = band(safe(lp.flags, lp) or 0, K.FL_DUCKING) ~= 0

    local fs_on = (CFG.aa_fs_always or bind_on(UI.k_aa_fs)) and not (air and CFG.aa_fs_noair)
    local edge_on = CFG.aa_edge and not air and not STATE.lp_moving
    if AA.t - AA.scan_t >= K.AA_SCAN_TICKS then
        AA.scan_t = AA.t
        AA.scan(eye, view)
        AA.fs_side = fs_on and AA.freestand(lp, eye) or 0
        AA.edge_yaw = edge_on and AA.edge(lp, eye) or nil
    end
    if not edge_on then AA.edge_yaw = nil end

    -- condition with fallbacks
    local si
    if air then si = duck and 8 or 6
    elseif duck then si = STATE.lp_moving and 7 or 5
    else si = AA.STATE_OF[RB.mstate or ST.STAND] or 2 end
    while si ~= 1 and not CFG[AA.KEYS[si].on] do si = AA.FALLBACK[si] or 1 end
    local k = AA.KEYS[si]
    if si ~= AA.cond then AA.cond, AA.hold_left = si, 0 end
    AA.advance(k)

    local yaw, src, static, force_down = nil, nil, false, false
    local m = AA.manual
    if m then
        yaw, src, static = cam + AA.MANUAL[m][2], AA.MANUAL[m][3], CFG.aa_manual_static
    elseif AA.knife_yaw then
        yaw, src, static = AA.knife_yaw, "KNIFE", true
    elseif fs_on and AA.fs_side ~= 0 and AA.at_yaw then
        yaw, src, static = AA.at_yaw + AA.fs_side * 90, "FREESTAND", CFG.aa_fs_static
    elseif AA.safe_head(kind, eye) then
        yaw, src, static, force_down = (AA.at_yaw or cam) + 180, "SAFE", true, true
    elseif AA.edge_yaw then
        yaw, src, static = AA.edge_yaw, "EDGE", true
    else
        yaw, src = ((CFG[k.base] == 2 and AA.at_yaw) or cam) + CFG[k.yaw], "BUILDER"
    end

    local hurt = CFG.aa_hurt and rt < AA.hurt_until
    local ab, abm = AA.ab_n, CFG.aa_ab
    local shift = (hurt and 1 or 0) + ((ab > 0 and abm == 2) and ab or 0)
    if not static then
        local add, sd = AA.modifier(k, shift)
        if sd > 0 then add = add + CFG[k.yaw_l] elseif sd < 0 then add = add + CFG[k.yaw_r] end
        yaw = yaw + add
    end
    if src == "BUILDER" then
        if hurt then yaw = yaw + AA.hurt_sign * CFG.aa_hurt_off end
        if ab > 0 then
            if abm == 3 then yaw = yaw + ((ab % 2 == 1) and 1 or -1) * CFG.aa_ab_off
            elseif abm == 4 then yaw = yaw + AA.AB_SEQ[(ab - 1) % #AA.AB_SEQ + 1] * CFG.aa_ab_off end
        end
    end

    local pm, pitch = CFG[k.pitch], view.x
    if force_down or pm == 2 then pitch = 89
    elseif pm == 3 then pitch = -89
    elseif pm == 4 then pitch = 0
    elseif pm == 5 then pitch = CFG[k.pitch_v]
    elseif pm == 6 then pitch = ((AA.phase + shift) % 2 == 0) and 89 or -89
    elseif pm == 7 then pitch = sin(rad(AA.t * 7)) * abs(CFG[k.pitch_v])
    elseif pm == 8 then pitch = (AA.rand3 * 2 - 1) * 89 end
    pitch, yaw = clamp(pitch, -89, 89), normalize(yaw)

    if not pcall(cmd.set_view_angles, cmd, vector(pitch, yaw, 0)) then
        AA.fails = AA.fails + 1
        if AA.fails >= K.AA_FAIL_LIMIT then
            AA.dead = true
            notify("Anti-aim stopped: cmd:set_view_angles is rejected. Save & Reload to try again.")
        end
        return AA.idle("ERROR")
    end
    AA.fails = 0
    AA.fix_movement(cmd, cam, yaw)
    if CFG.aa_lock then pcall(cmd.lock_angles, cmd) end

    AA.active, AA.why, AA.src = true, "ON", src
    AA.set_label((src == "BUILDER") and s_upper(ITEMS.AA_STATE[si]) or src)
end

-- Bullet damage taken from an enemy: shuffle (and it was not a miss for the anti-bruteforce).
function AA.on_player_hurt(ev)
    if not CFG.aa_on then return end
    local lc = entity.local_controller()
    local vic, att = safe(ev.get_controller, ev, "userid"), safe(ev.get_controller, ev, "attacker")
    if not lc or not vic or not att then return end
    local la = safe(lc.address, lc)
    if la == nil or safe(vic.address, vic) ~= la or safe(att.address, att) == la then return end
    if WPN.non_gun_name(safe(ev.get_string, ev, "weapon")) then return end
    AA.ab_pending = nil
    if not CFG.aa_hurt then return end
    AA.hurt_sign = -AA.hurt_sign
    AA.hurt_until = STATE.rt + CFG.aa_hurt_time
    VIS.push("info", "anti-aim shuffled (hit taken)")
end

-- Enemy gun shot whose eye angles point at us: candidate miss for the anti-bruteforce.
function AA.on_weapon_fire(ev)
    if not CFG.aa_on or CFG.aa_ab == 1 or not AA.active or AA.ab_pending then return end
    local pawn = safe(ev.get_pawn, ev, "userid")
    if not pawn or safe(pawn.is_enemy, pawn) ~= true then return end
    if WPN.non_gun_name(safe(ev.get_string, ev, "weapon")) then return end
    local lp = entity.local_pawn()
    if not lp then return end
    local from, to, ang = safe(pawn.eye_position, pawn), safe(lp.eye_position, lp), safe(pawn.eye_angles, pawn)
    if not from or not to or not ang then return end
    if U.fov(from, to, ang) <= K.AA_AB_FOV then AA.ab_pending = STATE.rt end
end

function AA.on_round_start()
    AA.ab_n, AA.ab_pending, AA.hurt_until = 0, nil, -1e9
end

function AA.reset()
    AA.at_yaw, AA.knife_yaw, AA.t_eye, AA.edge_yaw, AA.scan_t, AA.fs_side = nil, nil, nil, nil, -1e9, 0
    AA.hurt_until, AA.manual, AA.key_prev = -1e9, nil, {}
    AA.ab_n, AA.ab_pending = 0, nil
    AA.fails, AA.dead, AA.rot_ok = 0, false, true
end

-- ---------------------------------------------------------------- presets / builder actions
function AA.write_cond(i, values, on)
    for j = 1, #AA.FIELDS do
        local f = AA.FIELDS[j]
        local r = REG[AA.KEYS[i][f]]
        if r then
            local v = values and values[f]
            if f == "on" and on ~= nil then v = on end
            if v == nil then v = AA.DEFAULTS[f] end
            write_el(r, v)
        end
    end
end

function ACT.aa_preset_apply()
    local idx = CFG.aa_preset or 1
    local p = AA.PRESETS[idx]
    if not p then return end
    for i = 1, #AA.KEYS do AA.write_cond(i, p.s[i]) end
    if p.g then
        for id, v in pairs(p.g) do
            if REG[id] then write_el(REG[id], v) end
        end
    end
    cfg_tick(true)
    notify("Anti-aim preset applied: " .. tostring(ITEMS.AA_PRESET[idx]))
end

function ACT.aa_copy_shared()
    local edit = CFG.aa_edit or 1
    if edit == 1 then
        notify("Pick a condition other than Shared in 'Edit condition' first")
        return
    end
    local vals = {}
    for j = 1, #AA.FIELDS do vals[AA.FIELDS[j]] = CFG[AA.KEYS[1][AA.FIELDS[j]]] end
    AA.write_cond(edit, vals, true)
    cfg_tick(true)
    notify("Shared copied into " .. ITEMS.AA_STATE[edit])
end

function ACT.aa_reset_cond()
    local edit = CFG.aa_edit or 1
    AA.write_cond(edit, nil)
    cfg_tick(true)
    notify(ITEMS.AA_STATE[edit] .. " reset to defaults")
end

-- Arrow next to the crosshair: manual direction (accent) or freestanding side (amber).
function AA.arrows(P)
    if not (CFG.aa_arrows and AA.active) or STATE.sw <= 0 then return end
    local m, fs = AA.manual, AA.src == "FREESTAND"
    if not m and not fs then return end
    local tag = fs and (AA.fs_side > 0 and "LEFT" or "RIGHT") or AA.MANUAL[m][3]
    local col = fs and P.warn or P.acc
    local cx, cy, d, z = floor(STATE.sw * 0.5), floor(STATE.sh * 0.5), 46, 9
    if tag == "LEFT" then render.triangle_filled(cx - d - z, cy, cx - d, cy - z, cx - d, cy + z, col)
    elseif tag == "RIGHT" then render.triangle_filled(cx + d + z, cy, cx + d, cy - z, cx + d, cy + z, col)
    elseif tag == "BACK" then render.triangle_filled(cx, cy + d + z, cx - z, cy + d, cx + z, cy + d, col)
    else render.triangle_filled(cx, cy - d - z, cx - z, cy - d, cx + z, cy - d, col) end
end

-- ============================================================================
--  TETRIS (4.2)
--  Guideline rules: 10x20 well (+2 hidden rows), 7-bag randomizer, SRS rotation with wall
--  kicks, hold, ghost, lock delay with a move-reset cap, DAS / ARR, T-spins (3-corner rule),
--  combos and back-to-back. Isolation from the rest of the script:
--    · own random generator (never math.random), own db file, own menu tab
--    · logic and drawing run in paint only; nothing here runs in createmove / frame_stage
--    · the keyboard is read only while the game is visible and running; meanwhile
--      STATE.kb_captured freezes the manual anti-aim binds and the resolver flip bind
-- ============================================================================
TET.W, TET.H, TET.HIDDEN = 10, 22, 2
TET.LOCK_DELAY, TET.MAX_RESETS, TET.DAS, TET.ARR, TET.SOFT_IV = 0.5, 15, 0.17, 0.04, 0.045
TET.VK = { drop = 0x20, pause = 0x50, restart = 0x52 }
TET.KEYS = {
    { left = 0x25, right = 0x27, down = 0x28, cw = 0x26, cw2 = 0x58, ccw = 0x5A, hold = 0x43 },   -- arrows, X, Z, C
    { left = 0x41, right = 0x44, down = 0x53, cw = 0x57, cw2 = 0x4B, ccw = 0x4A, hold = 0x4C },   -- WASD, K, J, L
}
TET.NAMES, TET.LN_PTS, TET.TS_PTS = { "SINGLE", "DOUBLE", "TRIPLE", "TETRIS" }, { 100, 300, 500, 800 }, { 400, 800, 1200, 1600 }
TET.state, TET.board, TET.queue = "idle", {}, {}
TET.cur_id, TET.rot, TET.px, TET.py, TET.hold_id, TET.can_hold = nil, 0, 3, 0, nil, true
TET.score, TET.lines, TET.level, TET.combo, TET.b2b, TET.interval = 0, 0, 1, -1, false, 1
TET.acc, TET.lock_t, TET.resets, TET.low_y, TET.last_rot, TET.soft = 0, 0, 0, 0, false, false
TET.das_dir, TET.das_t, TET.arr_acc = 0, 0, 0
TET.msg, TET.msg_t, TET.last_rt = nil, -1e9, 0
TET.best, TET.best_dirty = { score = 0, lines = 0, games = 0 }, false
TET.embed_ok, TET.embed_t, TET.drag, TET.was_down, TET.canvas_shown = true, -1e9, nil, false, nil
TET.rng = U.rng(os.time() + 7919)

-- Piece ids: 1 I, 2 J, 3 L, 4 O, 5 S, 6 T, 7 Z. SHAPES[id][rot + 1] = { x1, y1, ... x4, y4 }
-- (0-based cells inside the SRS bounding box, y down). Rotation states are generated by
-- rotating the spawn state clockwise, which reproduces the true SRS states.
do
    local base = {
        { 4, { 0, 1, 1, 1, 2, 1, 3, 1 } }, { 3, { 0, 0, 0, 1, 1, 1, 2, 1 } }, { 3, { 2, 0, 0, 1, 1, 1, 2, 1 } },
        { 0, { 1, 0, 2, 0, 1, 1, 2, 1 } }, { 3, { 1, 0, 2, 0, 0, 1, 1, 1 } }, { 3, { 1, 0, 0, 1, 1, 1, 2, 1 } },
        { 3, { 0, 0, 1, 0, 1, 1, 2, 1 } },
    }
    TET.SHAPES = {}
    for id = 1, 7 do
        local size, rots = base[id][1], { base[id][2] }
        for r = 2, 4 do
            local prev, nxt = rots[r - 1], {}
            for i = 1, 7, 2 do
                if size == 0 then nxt[i], nxt[i + 1] = prev[i], prev[i + 1]
                else nxt[i], nxt[i + 1] = size - 1 - prev[i + 1], prev[i] end
            end
            rots[r] = nxt
        end
        TET.SHAPES[id] = rots
    end
    -- SRS wall kicks, key = from * 4 + to (0 spawn, 1 right, 2 reverse, 3 left); pairs are
    -- (dx, dy) with y UP as published in the guideline, dy is negated when applied.
    TET.KICK = {
        [1]  = { 0, 0, -1, 0, -1, 1, 0, -2, -1, -2 },  [4]  = { 0, 0, 1, 0, 1, -1, 0, 2, 1, 2 },
        [6]  = { 0, 0, 1, 0, 1, -1, 0, 2, 1, 2 },      [9]  = { 0, 0, -1, 0, -1, 1, 0, -2, -1, -2 },
        [11] = { 0, 0, 1, 0, 1, 1, 0, -2, 1, -2 },     [14] = { 0, 0, -1, 0, -1, -1, 0, 2, -1, 2 },
        [12] = { 0, 0, -1, 0, -1, -1, 0, 2, -1, 2 },   [3]  = { 0, 0, 1, 0, 1, 1, 0, -2, 1, -2 },
    }
    TET.KICK_I = {
        [1]  = { 0, 0, -2, 0, 1, 0, -2, -1, 1, 2 },    [4]  = { 0, 0, 2, 0, -1, 0, 2, 1, -1, -2 },
        [6]  = { 0, 0, -1, 0, 2, 0, -1, 2, 2, -1 },    [9]  = { 0, 0, 1, 0, -2, 0, 1, -2, -2, 1 },
        [11] = { 0, 0, 2, 0, -1, 0, 2, 1, -1, -2 },    [14] = { 0, 0, -2, 0, 1, 0, -2, -1, 1, 2 },
        [12] = { 0, 0, 1, 0, -2, 0, 1, -2, -2, 1 },    [3]  = { 0, 0, -1, 0, 2, 0, -1, 2, 2, -1 },
    }
    local rgb = { { 62, 199, 224 }, { 84, 110, 235 }, { 240, 150, 62 }, { 236, 206, 70 }, { 104, 204, 104 }, { 176, 96, 222 }, { 232, 84, 84 } }
    TET.COL, TET.GHOST = {}, {}
    for id = 1, 7 do
        TET.COL[id] = color(rgb[id][1], rgb[id][2], rgb[id][3], 255)
        TET.GHOST[id] = color(rgb[id][1], rgb[id][2], rgb[id][3], 60)
    end
    TET.C_WELL, TET.C_GRID, TET.C_SHADE = color(8, 9, 13, 235), color(255, 255, 255, 10), color(8, 9, 13, 170)
end

-- ---------------------------------------------------------------- rules
function TET.fits(id, rot, px, py)
    local s, board, W, H = TET.SHAPES[id][rot + 1], TET.board, TET.W, TET.H
    for i = 1, 7, 2 do
        local c, r = px + s[i] + 1, py + s[i + 1] + 1
        if c < 1 or c > W or r > H then return false end
        if r >= 1 and board[r][c] ~= 0 then return false end
    end
    return true
end

function TET.refill()
    local q, bag = TET.queue, { 1, 2, 3, 4, 5, 6, 7 }
    for i = 7, 2, -1 do
        local j = floor(TET.rng() * i) + 1
        bag[i], bag[j] = bag[j], bag[i]
    end
    for i = 1, 7 do q[#q + 1] = bag[i] end
end

function TET.set_level()
    local lv = min(20, (CFG.tet_level or 1) + floor(TET.lines / 10))
    TET.level = lv
    TET.interval = max(0.01, (0.8 - (lv - 1) * 0.007) ^ (lv - 1))     -- guideline gravity curve, s per row
end

function TET.game_over()
    TET.state = "over"
    local b = TET.best
    b.games = b.games + 1
    if TET.score > b.score then b.score = TET.score end
    if TET.lines > b.lines then b.lines = TET.lines end
    TET.best_dirty = true
    TET.save()
    TET.label()
end

function TET.spawn(id)
    if not id then
        if #TET.queue < 8 then TET.refill() end
        id = tremove(TET.queue, 1)
    end
    TET.cur_id, TET.rot, TET.px, TET.py = id, 0, 3, 0
    TET.acc, TET.lock_t, TET.resets, TET.low_y, TET.last_rot = 0, 0, 0, 0, false
    if not TET.fits(id, 0, 3, 0) then return TET.game_over() end         -- block out
    if TET.fits(id, 0, 3, 1) then TET.py = 1 end                          -- enter the well at once
end

function TET.new_game()
    for r = 1, TET.H do
        local row = TET.board[r] or {}
        for c = 1, TET.W do row[c] = 0 end
        TET.board[r] = row
    end
    TET.queue = {}
    TET.score, TET.lines, TET.combo, TET.b2b = 0, 0, -1, false
    TET.hold_id, TET.can_hold, TET.msg = nil, true, nil
    TET.das_dir, TET.das_t, TET.arr_acc, TET.soft = 0, 0, 0, false
    TET.set_level()
    TET.state = "play"
    TET.spawn()
end

-- A successful move or rotation restarts the lock delay, at most MAX_RESETS times per row.
function TET.touch(rotated)
    TET.last_rot = rotated
    if TET.resets < TET.MAX_RESETS then
        TET.lock_t, TET.resets = 0, TET.resets + 1
    end
end

function TET.move(dx)
    if not TET.fits(TET.cur_id, TET.rot, TET.px + dx, TET.py) then return false end
    TET.px = TET.px + dx
    TET.touch(false)
    return true
end

function TET.rotate(dir)
    local id, from = TET.cur_id, TET.rot
    if id == 4 then return false end                                       -- O does not rotate
    local to = (from + dir) % 4
    local kicks = ((id == 1) and TET.KICK_I or TET.KICK)[from * 4 + to]
    for i = 1, 9, 2 do
        local nx, ny = TET.px + kicks[i], TET.py - kicks[i + 1]
        if TET.fits(id, to, nx, ny) then
            TET.rot, TET.px, TET.py = to, nx, ny
            TET.touch(true)
            return true
        end
    end
    return false
end

function TET.ghost_y()
    local y = TET.py
    while TET.fits(TET.cur_id, TET.rot, TET.px, y + 1) do y = y + 1 end
    return y
end

function TET.hold()
    if not TET.can_hold then return end
    local prev = TET.hold_id
    TET.hold_id, TET.can_hold = TET.cur_id, false
    TET.spawn(prev)
end

function TET.lock()
    local id, s, board = TET.cur_id, TET.SHAPES[TET.cur_id][TET.rot + 1], TET.board
    local px, py, W, H = TET.px, TET.py, TET.W, TET.H
    -- T-spin: last move was a rotation and 3 of the 4 box corners are occupied
    local tspin = false
    if id == 6 and TET.last_rot then
        local n = 0
        for i = 0, 3 do
            local c, r = px + (i % 2) * 2 + 1, py + floor(i / 2) * 2 + 1
            if c < 1 or c > W or r > H or (r >= 1 and board[r][c] ~= 0) then n = n + 1 end
        end
        tspin = n >= 3
    end
    local visible = false
    for i = 1, 7, 2 do
        local c, r = px + s[i] + 1, py + s[i + 1] + 1
        if r >= 1 then board[r][c] = id end
        if r > TET.HIDDEN then visible = true end
    end
    local cleared, r = 0, H
    while r >= 1 do
        local row, full = board[r], true
        for c = 1, W do
            if row[c] == 0 then full = false break end
        end
        if full then
            tremove(board, r)
            for c = 1, W do row[c] = 0 end
            table.insert(board, 1, row)
            cleared = cleared + 1
        else
            r = r - 1
        end
    end

    local pts, name, hard = 0, nil, false
    if tspin then
        pts, hard = TET.TS_PTS[cleared + 1], cleared > 0
        name = "T-SPIN" .. (cleared > 0 and (" " .. TET.NAMES[cleared]) or "")
    elseif cleared > 0 then
        pts, name, hard = TET.LN_PTS[cleared], TET.NAMES[cleared], cleared == 4
    end
    if cleared > 0 then
        if hard and TET.b2b then pts, name = pts * 1.5, "B2B " .. name end
        TET.b2b = hard
        TET.combo = TET.combo + 1
        if TET.combo > 0 then
            pts = pts + 50 * TET.combo
            name = name .. "  x" .. (TET.combo + 1)
        end
        TET.lines = TET.lines + cleared
    else
        TET.combo = -1
    end
    if pts > 0 then TET.score = TET.score + floor(pts * TET.level) end
    if name then TET.msg, TET.msg_t = name, STATE.rt end
    TET.set_level()
    TET.can_hold = true
    if not visible then return TET.game_over() end                        -- lock out
    TET.spawn()
end

function TET.hard_drop()
    local y = TET.ghost_y()
    TET.score = TET.score + 2 * (y - TET.py)
    if y ~= TET.py then TET.last_rot = false end
    TET.py = y
    TET.lock()
end

function TET.step(dt)
    local id, rot, px = TET.cur_id, TET.rot, TET.px
    if not TET.fits(id, rot, px, TET.py + 1) then
        TET.acc, TET.lock_t = 0, TET.lock_t + dt
        if TET.lock_t >= TET.LOCK_DELAY then TET.lock() end
        return
    end
    local iv = TET.interval
    if TET.soft and iv > TET.SOFT_IV then iv = TET.SOFT_IV end
    TET.acc = TET.acc + dt / iv
    while TET.acc >= 1 do
        TET.acc = TET.acc - 1
        if not TET.fits(id, rot, px, TET.py + 1) then
            TET.acc = 0
            break
        end
        TET.py, TET.last_rot = TET.py + 1, false
        if TET.soft then TET.score = TET.score + 1 end
        if TET.py > TET.low_y then TET.low_y, TET.resets, TET.lock_t = TET.py, 0, 0 end
    end
end

-- ---------------------------------------------------------------- input
function TET.pressed(vk) return safe(input.key_pressed, vk) == true end
function TET.down(vk) return safe(input.key_down, vk) == true end

function TET.input(dt)
    local vk, st = TET.VK, TET.state
    if TET.pressed(vk.pause) and (st == "play" or st == "pause") then
        TET.state = (st == "play") and "pause" or "play"
        return
    end
    if st ~= "play" then
        if TET.pressed(vk.drop) and (st == "idle" or st == "over") then TET.new_game() end
        if TET.pressed(vk.restart) and st ~= "idle" then TET.new_game() end
        return
    end
    local k = TET.KEYS[CFG.tet_keys or 1] or TET.KEYS[1]
    if TET.pressed(k.hold) then TET.hold() end
    if TET.state ~= "play" then return end
    if TET.pressed(k.cw) or TET.pressed(k.cw2) then TET.rotate(1) end
    if TET.pressed(k.ccw) then TET.rotate(3) end
    -- horizontal: first step on press, then auto-repeat after DAS every ARR; the newest key wins
    local l, r = TET.down(k.left), TET.down(k.right)
    local dir = TET.das_dir
    if TET.pressed(k.left) then dir = -1 TET.das_t, TET.arr_acc = 0, 0 TET.move(-1)
    elseif TET.pressed(k.right) then dir = 1 TET.das_t, TET.arr_acc = 0, 0 TET.move(1) end
    if (dir == -1 and not l) or (dir == 1 and not r) then
        dir = (l and -1) or (r and 1) or 0
        TET.das_t, TET.arr_acc = 0, 0
    end
    TET.das_dir = dir
    if dir ~= 0 then
        TET.das_t = TET.das_t + dt
        if TET.das_t >= TET.DAS then
            TET.arr_acc = TET.arr_acc + dt
            while TET.arr_acc >= TET.ARR do
                TET.arr_acc = TET.arr_acc - TET.ARR
                if not TET.move(dir) then TET.arr_acc = 0 break end
            end
        end
    end
    TET.soft = TET.down(k.down)
    if TET.pressed(vk.drop) then TET.hard_drop() end
end

-- ---------------------------------------------------------------- drawing
function TET.draw_piece(bx, by, cell, id, rot, px, py, col)
    local s, hid = TET.SHAPES[id][rot + 1], TET.HIDDEN
    for i = 1, 7, 2 do
        local r = py + s[i + 1] + 1
        if r > hid then
            render.rect_filled(bx + (px + s[i]) * cell + 1, by + (r - hid - 1) * cell + 1, cell - 1, cell - 1, col)
        end
    end
end

function TET.draw_mini(x, y, cs, id, col)
    local s = TET.SHAPES[id][1]
    for i = 1, 7, 2 do
        render.rect_filled(x + s[i] * cs + 1, y + s[i + 1] * cs + 1, cs - 1, cs - 1, col)
    end
end

-- Whole game at (x, y): [hold + stats] [well] [next]. Width = 18 cells + 16, height = 20 cells.
function TET.draw(x, y, cell, P)
    local W, H, hid = TET.W, TET.H, TET.HIDDEN
    local side, ts = cell * 4, max(10, floor(cell * 0.72))
    local bx, by, bw, bh = x + side + 8, y, cell * W, cell * (H - hid)
    render.rect_filled(bx - 1, by - 1, bw + 2, bh + 2, TET.C_WELL)
    render.rect(bx - 1, by - 1, bw + 2, bh + 2, P.line, 0, 1)
    for c = 1, W - 1 do render.rect_filled(bx + c * cell, by, 1, bh, TET.C_GRID) end

    local st, board, col = TET.state, TET.board, TET.COL
    if st ~= "idle" then
        for r = hid + 1, H do
            local row, cy = board[r], by + (r - hid - 1) * cell
            for c = 1, W do
                local v = row[c]
                if v ~= 0 then render.rect_filled(bx + (c - 1) * cell + 1, cy + 1, cell - 1, cell - 1, col[v]) end
            end
        end
        local id = TET.cur_id
        if id and st ~= "over" then
            if CFG.tet_ghost then TET.draw_piece(bx, by, cell, id, TET.rot, TET.px, TET.ghost_y(), TET.GHOST[id]) end
            TET.draw_piece(bx, by, cell, id, TET.rot, TET.px, TET.py, col[id])
        end
    end

    -- left column: hold and numbers
    local cs = floor(cell * 0.8)
    VIS.text(x, y, P.key, "HOLD", ts)
    if TET.hold_id then TET.draw_mini(x, y + ts + 6, cs, TET.hold_id, TET.can_hold and col[TET.hold_id] or TET.GHOST[TET.hold_id]) end
    local ty = y + ts + 6 + cs * 3 + 8
    local rows = TET.stat_rows
    rows[2], rows[4], rows[6], rows[8] = tostring(TET.score), tostring(TET.lines), tostring(TET.level), tostring(TET.best.score)
    for i = 1, 7, 2 do
        VIS.text(x, ty, P.key, rows[i], ts)
        VIS.text(x, ty + ts + 2, (i == 1) and P.acc or P.val, rows[i + 1], ts)
        ty = ty + ts * 2 + 10
    end

    -- right column: next queue
    local nx = bx + bw + 8
    VIS.text(nx, y, P.key, "NEXT", ts)
    local q = TET.queue
    for i = 1, min(4, #q) do
        TET.draw_mini(nx, y + ts + 6 + (i - 1) * cs * 3, cs, q[i], col[q[i]])
    end

    -- state / message overlay
    local text = nil
    if st == "idle" then text = "SPACE  start"
    elseif st == "pause" then text = "PAUSED  ·  P"
    elseif st == "over" then text = "GAME OVER  ·  SPACE"
    elseif TET.msg and STATE.rt - TET.msg_t < 1.2 then text = TET.msg end
    if text then
        local tw = VIS.measure(text, ts)
        local my = by + floor(bh * (st == "play" and 0.18 or 0.42))
        if st ~= "play" then render.rect_filled(bx, by, bw, bh, TET.C_SHADE) end
        render.rect_filled(bx, my - 4, bw, ts + 10, TET.C_WELL)
        VIS.text(bx + floor((bw - tw) * 0.5), my, (st == "play") and P.acc or P.val, text, ts)
    end
end
TET.stat_rows = { "SCORE", "0", "LINES", "0", "LEVEL", "1", "BEST", "0" }

function TET.commit_drag(w, h)
    local d = TET.drag
    local nx = clamp(round(d.x / max(1, STATE.sw - w) * 100), 0, 100)
    local ny = clamp(round(d.y / max(1, STATE.sh - h) * 100), 0, 100)
    if REG.tet_x then write_el(REG.tet_x, nx) end
    if REG.tet_y then write_el(REG.tet_y, ny) end
    CFG.tet_x, CFG.tet_y = nx, ny
    TET.drag = nil
    SET.dirty, SET.dirty_t = true, STATE.rt
end

-- Window position; draggable by the title bar while the menu is open.
function TET.position(w, h, bar)
    local x = floor((STATE.sw - w) * CFG.tet_x / 100)
    local y = floor((STATE.sh - h) * CFG.tet_y / 100)
    local d = TET.drag
    if STATE.menu_open then
        local ok, mx, my = pcall(input.cursor)
        local down = TET.down(K.VK_LBUTTON)
        if ok and type(mx) == "number" and type(my) == "number" then
            if d then
                if down then
                    d.x = clamp(mx - d.dx, 0, max(0, STATE.sw - w))
                    d.y = clamp(my - d.dy, 0, max(0, STATE.sh - h))
                else
                    TET.commit_drag(w, h)
                end
            elseif down and not TET.was_down and not VIS.drag and mx >= x and mx <= x + w and my >= y and my <= y + bar
                and not VIS.over_menu(mx, my) then
                TET.drag = { dx = mx - x, dy = my - y, x = x, y = y }
            end
        end
        TET.was_down = down
    else
        if d then TET.commit_drag(w, h) end
        TET.was_down = false
    end
    d = TET.drag
    if d then return d.x, d.y end
    return x, y
end

function TET.window(P)
    if STATE.sw <= 0 or STATE.sh <= 0 then return end
    local cell = max(8, floor(16 * CFG.tet_scale / 100))
    local pad, bar = 10, 24
    local w, h = cell * 18 + 16 + pad * 2, cell * 20 + pad * 2 + bar
    local x, y = TET.position(w, h, bar)
    render.rect_filled(x, y, w, h, P.bg, 7)
    render.rect(x, y, w, h, P.line, 7, 1)
    VIS.text(x + pad, y + 5, P.acc, "0x", 14)
    VIS.text(x + pad + 22, y + 7, P.key, "tetris", 12)
    render.line(x + pad, y + bar, x + w - pad, y + bar, P.line, 1)
    TET.draw(x + pad, y + bar + pad, cell, P)
end

-- ui.custom callback (menu tab). If the menu cannot host render.* calls the first error
-- switches the game to the floating window for good.
function TET.embed_draw(x, y, w, h)
    if STATE.failed or not TET.embed_ok then return end
    TET.embed_t = globals.realtime()
    if CFG.tet_view ~= 2 then return end
    if type(x) ~= "number" or type(y) ~= "number" or type(w) ~= "number" or type(h) ~= "number" then return end
    local P = VIS.palette("pal_full", 255)
    local ok, err
    if CFG.tet_on then
        local cell = max(6, floor(min((w - 16) / 18, h / 20)))
        ok, err = pcall(TET.draw, x + floor((w - cell * 18 - 16) * 0.5), y, cell, P)
    else
        ok, err = pcall(VIS.text, x + 4, y + 4, P.key, "Tick 'Show Tetris' to play here", 12)
    end
    if not ok then
        TET.embed_ok = false
        TET.canvas_shown = nil
        say("Tetris cannot draw inside the menu (" .. tostring(err) .. "); the floating window is used instead")
    end
end

-- The canvas only takes space in the tab while the embedded display is selected.
function TET.sync_menu()
    if TET.embed_ok and is_dummy(UI.tet_canvas) then TET.embed_ok = false end   -- build without ui.custom
    local want = CFG.tet_view == 2 and TET.embed_ok
    if want == TET.canvas_shown then return end
    TET.canvas_shown = want
    local el = UI.tet_canvas
    if el and not is_dummy(el) then pcall(el.visible, el, want) end
end

-- Per-frame entry point (paint).
function TET.frame(rt, P)
    local dt = clamp(rt - TET.last_rt, 0, 0.1)
    TET.last_rt = rt
    if TET.canvas_shown == nil then TET.sync_menu() end
    local embed = CFG.tet_view == 2 and TET.embed_ok and STATE.menu_open
    local visible = CFG.tet_on and (STATE.menu_open or CFG.tet_ingame)
    if visible and embed and rt - TET.embed_t > 0.25 then visible = false end   -- another tab is shown
    if not visible then
        if TET.state == "play" then TET.state = "pause" end
        STATE.kb_captured = false
        if TET.drag then TET.drag = nil end
        return
    end
    TET.input(dt)
    if TET.state == "play" then TET.step(dt) end
    STATE.kb_captured = (TET.state == "play")
    if not embed then TET.window(P) end
end

-- ---------------------------------------------------------------- records / actions
function TET.label()
    local el, b = UI.tet_stats, TET.best
    if el and not is_dummy(el) then
        pcall(el.set, el, format("best %d · most lines %d · games %d", b.score, b.lines, b.games))
    end
end

function TET.load()
    local data = safe(db.load, META.db_tetris, nil)
    if type(data) == "table" then
        local b = TET.best
        for k in pairs(b) do
            local v = tonumber(data[k])
            if v and v >= 0 and v < 1e12 then b[k] = floor(v) end
        end
    end
    TET.label()
end

function TET.save()
    if not TET.best_dirty then return end
    if safe(db.save, META.db_tetris, TET.best) ~= false then TET.best_dirty = false end
end

function ACT.tet_new()
    if REG.tet_on and not CFG.tet_on then
        write_el(REG.tet_on, true)
        cfg_tick(true)
    end
    TET.new_game()
end

function ACT.tet_pause()
    if TET.state == "play" then TET.state = "pause"
    elseif TET.state == "pause" then TET.state = "play" end
end

function ACT.tet_wipe()
    TET.best.score, TET.best.lines, TET.best.games = 0, 0, 0
    TET.best_dirty = true
    TET.save()
    TET.label()
    notify("Tetris records cleared")
end

-- ============================================================================
--  LIFECYCLE
--  One guard per handler (4.2: counters are per handler, not per event name, so a healthy
--  handler can no longer hide a failing one that shares its event). Order inside a tick:
--    createmove : local state -> rage assist -> anti-aim
--    frame_stage: settings -> resolver (net update end) / re-apply (lag compensation)
--    paint      : background tasks -> visuals -> tetris (isolated, own error budget)
-- ============================================================================
local EVENTS = {}

-- A burst of errors: ragebot values are restored, the script pauses and tries again.
-- Only after ERR_STRIKES suspensions in a row does it stop until Save & Reload.
local function trip(name)
    STATE.strikes, STATE.strike_t = STATE.strikes + 1, STATE.rt
    STATE.kb_captured = false
    pcall(Bind.release, true)
    pcall(RB.reset)
    pcall(Journal.flush, true)
    RB.paused = false
    if STATE.strikes >= K.ERR_STRIKES then
        STATE.failed = true
        pcall(ESPX.remove)
        notify("Too many errors in '" .. name .. "': 0x stopped, ragebot values restored. Fix the cause and Save & Reload.")
    else
        STATE.suspend_until = STATE.rt + K.ERR_COOLDOWN
        notify(format("Errors in '%s': 0x suspended for %d s, ragebot values restored.", name, K.ERR_COOLDOWN))
    end
end

-- Every callback error is caught here and never reaches the game.
local function guard(name, fn)
    local errs, prof = STATE.errs, STATE.prof
    errs[name] = 0
    return function(a, b, c)
        if STATE.failed then return end
        local rt = globals.realtime()
        STATE.rt = rt
        if STATE.suspend_until then
            if rt < STATE.suspend_until then return end
            STATE.suspend_until = nil
        end
        local ok, err = pcall(fn, a, b, c)
        if CFG.debug then                                   -- smoothed cost per call, ms (debug panel)
            prof[name] = (prof[name] or 0) * 0.95 + (globals.realtime() - rt) * 50
        end
        if ok then
            if errs[name] ~= 0 then errs[name] = 0 end
            return
        end
        report(name, err)
        local n = errs[name] + 1
        errs[name] = n
        if n >= K.ERR_LIMIT then
            errs[name] = 0
            trip(name)
        end
    end
end

local function hook(event, tag, fn)
    local name = tag and (event .. ":" .. tag) or event
    local ok, id = pcall(events.on, event, guard(name, fn))
    if ok and id ~= nil then
        EVENTS[#EVENTS + 1] = id
    else
        say("event '" .. event .. "' not available: " .. tostring(id))
    end
end

local LIFE = {}

-- Createmove: capture the angles actually sent, refresh local state, run rage assist and anti-aim.
function LIFE.createmove(cmd)
    local a = safe(cmd.view_angles, cmd)
    if a then STATE.cmd_angles = vector(a.x, a.y, 0) end
    local lp = entity.local_pawn()
    if lp and safe(lp.alive, lp) == true then
        RB.movement(lp, cmd)
        RES.sample_spread(lp)
    else
        lp = nil
        STATE.lp_air, STATE.lp_moving, RB.mstate = false, false, nil
    end
    STATE.lp_dead = (lp == nil)
    if STATE.rt - RB.paint_t > K.PAINT_TIMEOUT then RB.background(STATE.rt) end
    RB.tick(cmd, lp)
    AA.run(cmd, lp)
end

-- Tetris runs inside its own pcall: a fault there never counts against the combat modules.
function LIFE.tetris(now)
    if TET.dead then return end
    local ok, err = pcall(TET.frame, now, VIS.palette("pal_full", 255))
    if ok then
        TET.errs = 0
        return
    end
    report("tetris", err)
    TET.errs = (TET.errs or 0) + 1
    if TET.errs >= 5 then
        TET.dead, STATE.kb_captured = true, false
        notify("Tetris stopped after repeated errors; the rest of 0x is unaffected. Save & Reload to try again.")
    end
end

function LIFE.paint()
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
    LIFE.tetris(now)
end

function LIFE.round_start()
    RES.on_round_start()
    AA.on_round_start()
end

function LIFE.level_init()
    RES.on_level_init()
    RB.on_level()
    AA.reset()
end

function LIFE.level_shutdown()
    RES.on_level_shutdown()
    RB.on_level()
    AA.reset()
end

function LIFE.unload()
    STATE.rt = globals.realtime()
    STATE.kb_captured = false
    pcall(ESPX.remove)
    pcall(RB.on_unload)
    pcall(RES.store_save, false)
    pcall(TET.save)
    if SET.dirty then pcall(IO.save) end
    for i = 1, #EVENTS do pcall(events.off, EVENTS[i]) end
    say("unloaded")
end

function LIFE.boot()
    STATE.rt = globals.realtime()
    local ok_dt, dt = pcall(globals.interval)
    if ok_dt and type(dt) == "number" and dt > 0 then RB.g_tick = K.GRAVITY * dt end
    local sw, sh = render.screen_size()
    if type(sw) == "number" and type(sh) == "number" then STATE.sw, STATE.sh = sw, sh end

    VIS.init()
    build_menu()

    IO.load()                                    -- snapshot first: it may carry manual paths
    local restored = Journal.restore()
    local scanned = Bind.scan()
    RB.boot_status = scanned and Bind.summary() or "config.keys unavailable"
    RB.set_status(RB.boot_status)

    PS.last = nil
    cfg_tick(true)
    PS.last = CFG.preset
    SET.dirty = SET.migrated == true             -- v3 / s1 import: write the current snapshot once

    RES.store_load()
    TET.load()
    RES.insecure = safe(client.insecure) == true
    STATE.insecure = RES.insecure
    local ok, open = pcall(input.menu_open)
    STATE.menu_open = ok and open == true
    ESPX.sync()

    hook("frame_stage",    nil,   RES.frame)
    hook("createmove",     nil,   LIFE.createmove)
    hook("paint",          nil,   LIFE.paint)
    hook("weapon_fire",    "res", RES.on_weapon_fire)
    hook("weapon_fire",    "aa",  AA.on_weapon_fire)
    hook("player_hurt",    "res", RES.on_player_hurt)
    hook("player_hurt",    "aa",  AA.on_player_hurt)
    hook("player_death",   nil,   RES.on_player_death)
    hook("round_start",    nil,   LIFE.round_start)
    hook("menu_toggled",   nil,   RB.on_menu_toggled)
    hook("level_init",     nil,   LIFE.level_init)
    hook("level_shutdown", nil,   LIFE.level_shutdown)
    local uok, uerr = pcall(events.on, "unload", LIFE.unload)
    if not uok then say("unload hook failed: " .. tostring(uerr)) end

    if restored > 0 then notify("Restored " .. restored .. " ragebot values after a crash") end
    local cb = MENU.combo_base
    say(format("v%s loaded · insecure=%s · paths: %s · combo base: %s", META.version, tostring(STATE.insecure),
        RB.boot_status, cb == 0 and "0" or (cb == 1 and "1" or "by name")))
    if scanned and Bind.total() == 0 then
        notify("No ragebot paths found in config. Use 'Dump paths to console' on the 0x Rage tab.")
    else
        notify(format("%s v%s loaded · %s", META.name, META.version, META.credits))
    end
end

local boot_ok, boot_err = pcall(LIFE.boot)
if not boot_ok then
    STATE.failed = true
    pcall(Bind.release, true)
    pcall(Journal.flush, true)
    say("boot error: " .. tostring(boot_err))
end
