--// Boss Spectator PRO v9.5.2 - HARD ANTI-JITTER + STREAM + PERSISTENT MORPH
--// Q - spectate, O/P - next/prev, I - first-person, M - freecam, V - 3rd person, K - UI, R - RESET
--// F2 - hide other UI, F7 - DIM, L - TP, N - GOD MODE, F5 - light, F6 - SUPER light
--// ★ F1 - MORPH into the locked boss (client-side visual). Persists until F1 again.
--// ★ J - follow boss rotation | 2xW - sprint | 2xT - freecam boost | Wheel - zoom | RMB - rotate
--// ★ FP: Wheel - zoom | SPACE - up | LShift - down
--// ★★ snapshot buffer + interpolation delay = zero-jitter boss tracking
--// ★★★ v9.3.0: StreamAroundBoss — request streaming around boss during spectate
--// ★★★ v9.4.0: F1 MORPH — visually become the locked boss
--// ★★★ v9.5.0: MORPH now PERSISTS through respawn, death, and any camera mode
--// ★★★ v9.5.1: Added "mickey" (and more) to BOSS_NAME_PATTERNS
--// ★★★ v9.5.2: LAG FIX (no feature distortion):
--//     • INTERP_DELAY 0.10 → 0.04  (camera 40ms behind instead of 100ms — feels responsive, still smooths jitter)
--//     • STREAM_REQUEST_INTERVAL 1.5 → 4.0  (less network chatter / micro-stutter)
--//     • Cached boss Head/orient reference  (NO more recursive FindFirstChild every single frame — big CPU win)
--//     • Periodic head cache refresh every ~2s from Heartbeat (safe fallback to HumanoidRootPart)

print("[BOSS] v9.5.2 boot...")

local Players          = game:GetService("Players")
local UIS              = game:GetService("UserInputService")
local RunService       = game:GetService("RunService")
local Workspace        = game:GetService("Workspace")
local Lighting         = game:GetService("Lighting")
local StarterGui       = game:GetService("StarterGui")
local CollectionService= game:GetService("CollectionService")

local player = Players.LocalPlayer
local camera = workspace.CurrentCamera

-- ============= CONFIG =============
local CAMERA_DISTANCE        = 14
local MIN_DISTANCE           = 3
local MAX_DISTANCE           = 50
local CAMERA_HEIGHT_OFFSET   = 2
local FP_EYE_HEIGHT          = 1.5
local SENSITIVITY            = 0.003
local FREECAM_SPEED          = 20
local FREECAM_BOOST_SPEED    = 65
local BOSS_REFRESH_INTERVAL  = 15.0
local INCREMENTAL_DELAY      = 1.0
local SPRINT_SPEED           = 32
local DOUBLE_TAP_TIME        = 0.3
local SCAN_YIELD_EVERY       = 200

local STATIC_MOVEMENT_THRESHOLD = 1.0
local STATIC_SCANS_LIMIT        = 2

local TP_YAW_FOLLOW_SPEED    = 5.0

local DIM_BRIGHTNESS_MUL  = 0.5
local DIM_AMBIENT_MUL     = 0.6
local DIM_OUTDOOR_MUL     = 0.6
local DIM_EXPOSURE_DELTA  = -1.2

local MOUSE_LOCK_MODE = "LockCenter"

local GOD_HEALTH = 1000000

-- FP manual adjustments
local FP_ZOOM_STEP  = 0.5
local FP_ZOOM_MIN   = -10
local FP_ZOOM_MAX   = 15
local FP_UP_SPEED   = 4
local FP_UP_MIN     = -8
local FP_UP_MAX     = 20

local FOLLOW_ROT_SPEED = 8.0

-- ★★★ HARD ANTI-JITTER (snapshot buffer + interpolation delay) ★★★
-- v9.5.2: lowered from 0.10 → 0.04 to remove the "screen lags behind" feeling.
-- 40ms is still ~2-3 frames of buffer at 60fps: smooths network jitter, responsive camera.
local INTERP_DELAY    = 0.04
local SNAP_MAX        = 60
local TELEPORT_DIST   = 200
local SNAP_EPSILON    = 0.01

-- ★★★ STREAM FIX CONFIG ★★★
-- v9.5.2: 1.5 → 4.0 — RequestStreamAroundAsync is a network call, spamming it caused micro-stutters.
local STREAM_REQUEST_INTERVAL = 4.0
local STREAM_REQUEST_TIMEOUT  = 2

-- ★★★ MORPH CONFIG ★★★
local MORPH_Y_OFFSET = 0
-- ==================================

local spectating     = true
local firstPerson    = false
local freecam        = false
local uiVisible      = true
local isRightMouseDown = false

local godMode            = false
local godModeConns       = {}
local godModeLastChar    = nil

local thirdPerson    = false
local tpDistance     = 10
local TP_MIN, TP_MAX = 3, 30

local hideOtherUI    = false
local hiddenGuis     = {}

local sprintEnabled      = false
local freecamBoost       = false
local lastWTime          = 0
local lastTTime          = 0
local originalWalkSpeed  = nil

local followBossRotation = false

local bosses     = {}
local bossInfo   = {}
local currentIndex = 1
local lockedBoss = nil
local lockedBossRoot = nil
local lastKnownBossPosition = nil
local lastKnownBossName = "None"

-- ★ v9.5.2: cached boss orientation reference (avoids per-frame recursive FindFirstChild)
local cachedBossHead    = nil
local cachedBossOrient  = nil

-- snapshot buffer state
local snapshots       = {}
local lastAcceptedPos = nil
local eyeYOffset      = nil

-- stream fix state
local lastStreamRequest = 0

-- ★ morph state (PERSISTENT)
local morphModel              = nil
local morphedBossName         = nil
local savedCharacterTransparency = {}   -- [instance] = original Transparency
local morphHideConn           = nil     -- DescendantAdded listener for current character

local yaw, pitch = 0, 0
local distance   = CAMERA_DISTANCE
local freecamPosition = nil

local camDirty = true
local cachedRot = CFrame.new()
local cachedOffset = Vector3.new(0, 0, 0)
local lastFramePos = nil
local HEIGHT_OFFSET_V = Vector3.new(0, CAMERA_HEIGHT_OFFSET, 0)

local fpZoomOffset = 0
local fpUpOffset   = 0

local rotationDeltaX, rotationDeltaY = 0, 0
local accMouseDx, accMouseDy = 0, 0
local lastMouseX, lastMouseY = nil, nil

local lightEnabled, lightPart = false, nil
local lightMode = "none"
local superLightPart = nil
local savedLightingState = nil

----------------------------------------------------
-- GUI
----------------------------------------------------
local playerGui = player:WaitForChild("PlayerGui")

local gui = Instance.new("ScreenGui")
gui.Name = "BossSpectatorUI"
gui.ResetOnSpawn = false
gui.Parent = playerGui

local mainFrame = Instance.new("Frame")
mainFrame.Size = UDim2.new(0, 340, 0, 540)
mainFrame.Position = UDim2.new(0.02, 0, 0.10, 0)
mainFrame.BackgroundColor3 = Color3.fromRGB(25, 25, 25)
mainFrame.BorderSizePixel = 0
mainFrame.Parent = gui
Instance.new("UICorner", mainFrame).CornerRadius = UDim.new(0, 10)

local title = Instance.new("TextLabel")
title.Size = UDim2.new(1, 0, 0, 40); title.BackgroundTransparency = 1
title.Text = "BOSS SPECTATOR v9.5.2"
title.Font = Enum.Font.GothamBold; title.TextSize = 20
title.TextColor3 = Color3.new(1, 1, 1); title.Parent = mainFrame

local currentLabel = Instance.new("TextLabel")
currentLabel.Size = UDim2.new(1, -20, 0, 25)
currentLabel.Position = UDim2.new(0, 10, 0, 45)
currentLabel.BackgroundTransparency = 1
currentLabel.Text = "Current: None"
currentLabel.Font = Enum.Font.Gotham; currentLabel.TextSize = 14
currentLabel.TextColor3 = Color3.fromRGB(0, 255, 170)
currentLabel.TextXAlignment = Enum.TextXAlignment.Left
currentLabel.Parent = mainFrame

local __lastLabelText = "Current: None"
local __labelStatus, __labelName = nil, nil
local function setLabel(txt)
    if txt ~= __lastLabelText then
        __lastLabelText = txt
        currentLabel.Text = txt
    end
end

local scroll = Instance.new("ScrollingFrame")
scroll.Size = UDim2.new(1, -20, 0, 260)
scroll.Position = UDim2.new(0, 10, 0, 80)
scroll.BackgroundColor3 = Color3.fromRGB(35, 35, 35)
scroll.BorderSizePixel = 0; scroll.ScrollBarThickness = 6
scroll.Parent = mainFrame
Instance.new("UICorner", scroll).CornerRadius = UDim.new(0, 8)

local layout = Instance.new("UIListLayout")
layout.Parent = scroll; layout.Padding = UDim.new(0, 5)

local hint = Instance.new("TextLabel")
hint.Size = UDim2.new(1, -20, 0, 195)
hint.Position = UDim2.new(0, 10, 0, 345)
hint.BackgroundTransparency = 1
hint.Text = "Q - spectate | O/P - prev/next | I - first-person\n" ..
            "M - freecam | V - 3rd person | K - UI\n" ..
            "F2 - hide other UI | F7 - DIM\n" ..
            "L - TP | N - GOD | F1 - MORPH boss (persists!)\n" ..
            "J - follow boss rotation\n" ..
            "R - RESET camera (morph stays)\n" ..
            "F5 - light | F6 - SUPER light\n" ..
            "2xW - sprint | 2xT - freecam boost\n" ..
            "RMB - rotate | Wheel - zoom\n" ..
            "FP: Wheel - zoom | SPACE - up | LShift - down"
hint.Font = Enum.Font.Gotham; hint.TextSize = 11
hint.TextColor3 = Color3.fromRGB(200, 200, 200)
hint.TextXAlignment = Enum.TextXAlignment.Left
hint.TextYAlignment = Enum.TextYAlignment.Top
hint.Parent = mainFrame

print("[BOSS] GUI ready")

----------------------------------------------------
-- PATTERNS / DETECTION
----------------------------------------------------
local BOSS_NAME_PATTERNS = {
    "boss", "eli", "enemy", "monster", "raid", "dummy", "npc", "mob",
    "titan", "guardian", "king", "queen", "lord", "demon", "dragon",
    "master", "nemesis", "slayer", "beast", "brute", "warlord",
    "overlord", "champion", "elite", "miniboss", "megaboss", "worldboss",
    "phantom", "specter", "wraith", "revenant", "nightmare", "horror",
    "abomination", "creature", "entity", "primordial", "falcity", "mythic",
    "legendary", "avatar", "deity", "god", "colossus", "verity", "ogre",
    "troll", "wyvern", "hydra", "kraken", "reaper", "hunter", "assassin",
    "skeleton", "carnival", "ghost", "terror", "werewolf", "gargoyle",
    "dumpling", "squishy", "sammy",
    "mickey", "mouse", "minnie", "donald", "goofy", "pluto",
    "cartoon", "toon", "animatronic", "fnaf", "freddy", "bonnie",
    "chica", "foxy", "springtrap", "puppet", "marionette",
    "clown", "jester", "pierrot", "harlequin",
}

local ROOT_NAME_CANDIDATES = {
    "HumanoidRootPart", "UpperTorso", "LowerTorso", "Torso",
    "RootPart", "Root", "Body", "Head", "Pelvis", "Chest", "Hips",
    "Humanoid",
}

local nameMatchCache = {}
local function matchesBossName(name)
    if not name or name == "" then return false end
    local c = nameMatchCache[name]
    if c ~= nil then return c end
    local lower = string.lower(name)
    local result = false
    for i = 1, #BOSS_NAME_PATTERNS do
        if string.find(lower, BOSS_NAME_PATTERNS[i], 1, true) then result = true; break end
    end
    nameMatchCache[name] = result
    return result
end

local function getRoot(model)
    if not model or not model:IsA("Model") then return nil end
    for _, n in ipairs(ROOT_NAME_CANDIDATES) do
        local p = model:FindFirstChild(n, true)
        if p and p:IsA("BasePart") then return p end
    end
    if model.PrimaryPart and model.PrimaryPart:IsA("BasePart") then
        return model.PrimaryPart
    end
    return model:FindFirstChildWhichIsA("BasePart", true)
end

local function isJunkModel(model)
    if not model or not model:IsA("Model") then return true end
    if model:IsA("Accessory") then return true end
    if model.Name == "Debris" then return true end
    if model:GetAttribute("__BossSpectatorMorph") then return true end
    if model:FindFirstChildWhichIsA("Tool") then return true end
    local parent = model.Parent
    if parent and Players:GetPlayerFromCharacter(parent) then return true end
    if Players:GetPlayerFromCharacter(model) then return true end
    return false
end

local function checkTagOrAttr(inst)
    local okT, tags = pcall(function() return CollectionService:GetTags(inst) end)
    if okT and tags then
        for _, tag in ipairs(tags) do
            local lt = string.lower(tag)
            for _, pat in ipairs(BOSS_NAME_PATTERNS) do
                if string.find(lt, pat, 1, true) then return true, "tag:" .. tag end
            end
        end
    end
    local okA, attrs = pcall(function() return inst:GetAttributes() end)
    if okA and attrs then
        for name, value in pairs(attrs) do
            local ln = string.lower(name)
            if (ln == "isboss" or ln == "boss" or ln == "is_boss") and value == true then
                return true, "attribute"
            end
            if ln == "type" or ln == "entitytype" or ln == "class"
               or ln == "kind" or ln == "category" then
                local lv = string.lower(tostring(value))
                for _, pat in ipairs(BOSS_NAME_PATTERNS) do
                    if string.find(lv, pat, 1, true) then return true, "attribute" end
                end
            end
        end
    end
    return false, nil
end

local function classifyBoss(model)
    if not model or not model:IsA("Model") then return false, "not-model", nil, false, false end
    if isJunkModel(model) then return false, "junk", nil, false, false end
    if Players:GetPlayerFromCharacter(model) then return false, "player", nil, false, false end

    local root = getRoot(model)
    if not root then return false, "no-root", nil, false, false end

    local hasHum  = model:FindFirstChildWhichIsA("Humanoid", true) ~= nil
    local hasAnim = model:FindFirstChildWhichIsA("AnimationController", true) ~= nil

    if hasHum then return true, "humanoid", root, true, hasAnim end
    if matchesBossName(model.Name) then return true, "name", root, false, hasAnim end
    if model.PrimaryPart and matchesBossName(model.PrimaryPart.Name) then
        return true, "primary-name", root, false, hasAnim
    end
    if hasAnim then return true, "animctrl", root, false, true end

    local tagOk, tagReason = checkTagOrAttr(model)
    if tagOk then return true, tagReason, root, false, hasAnim end

    return false, "no-match", root, hasHum, hasAnim
end

----------------------------------------------------
-- SNAPSHOT BUFFER
----------------------------------------------------
local function resetSmoothing()
    snapshots       = {}
    lastAcceptedPos = nil
    eyeYOffset      = nil
end

local function pushBossSnapshot(pos, now)
    if not pos then return end
    if lastAcceptedPos then
        local delta = (pos - lastAcceptedPos).Magnitude
        if delta > TELEPORT_DIST then
            snapshots = { {t = now, p = pos} }
            lastAcceptedPos = pos
            return
        end
    end
    local last = snapshots[#snapshots]
    if last and (last.p - pos).Magnitude < SNAP_EPSILON then
        return
    end
    table.insert(snapshots, {t = now, p = pos})
    while #snapshots > SNAP_MAX do
        table.remove(snapshots, 1)
    end
    lastAcceptedPos = pos
end

local function sampleBossSnapshot(now, fallback)
    if #snapshots == 0 then return fallback end
    if #snapshots == 1 then return snapshots[1].p end
    local rt = now - INTERP_DELAY
    if rt <= snapshots[1].t then return snapshots[1].p end
    if rt >= snapshots[#snapshots].t then return snapshots[#snapshots].p end
    for i = 2, #snapshots do
        if snapshots[i].t >= rt then
            local a = snapshots[i - 1]
            local b = snapshots[i]
            local span = b.t - a.t
            local alpha = (span > 0.0001) and ((rt - a.t) / span) or 1
            return a.p:Lerp(b.p, alpha)
        end
    end
    return snapshots[#snapshots].p
end

local function computeEyeYOffset()
    eyeYOffset = FP_EYE_HEIGHT
    if not lockedBoss or not lockedBossRoot then return end
    local head = lockedBoss:FindFirstChild("Head", true)
    if head and head:IsA("BasePart") and lockedBossRoot.Parent then
        local dy = head.Position.Y - lockedBossRoot.Position.Y
        local bonus = head.Size.Y * 0.35
        eyeYOffset = dy + bonus
    end
end

----------------------------------------------------
-- v9.5.2: BOSS ORIENT CACHE (fixes per-frame FindFirstChild lag)
----------------------------------------------------
-- Refreshes cached Head/orient reference. Called on lock and from Heartbeat (~every 2s).
local function refreshOrientCache()
    cachedBossHead = nil
    cachedBossOrient = nil
    if not lockedBoss or not lockedBoss.Parent then return end
    local h = lockedBoss:FindFirstChild("Head", true)
    if h and h:IsA("BasePart") then
        cachedBossHead = h
        cachedBossOrient = h
    elseif lockedBossRoot and lockedBossRoot.Parent then
        cachedBossOrient = lockedBossRoot
    end
end

-- Fast getter (no FindFirstChild — only cached checks).
local function getBossOrient()
    if cachedBossHead and cachedBossHead.Parent then return cachedBossHead end
    if cachedBossOrient and cachedBossOrient.Parent then return cachedBossOrient end
    if lockedBossRoot and lockedBossRoot.Parent then
        cachedBossOrient = lockedBossRoot
        return lockedBossRoot
    end
    return nil
end

----------------------------------------------------
-- STREAM FIX
----------------------------------------------------
local function requestStreamAroundBoss(force)
    if not spectating then return end
    local pos = nil
    if lockedBossRoot and lockedBossRoot.Parent then
        pos = lockedBossRoot.Position
    elseif lastKnownBossPosition then
        pos = lastKnownBossPosition
    end
    if not pos then return end

    local now = os.clock()
    if not force and (now - lastStreamRequest) < STREAM_REQUEST_INTERVAL then
        return
    end
    lastStreamRequest = now

    task.spawn(function()
        pcall(function()
            player:RequestStreamAroundAsync(pos, STREAM_REQUEST_TIMEOUT)
        end)
    end)
end

----------------------------------------------------
-- MORPH HELPERS (persistent visual morph)
----------------------------------------------------
local function hideCharacterForMorph(char)
    if not char then return end

    if morphHideConn then
        pcall(function() morphHideConn:Disconnect() end)
        morphHideConn = nil
    end

    local function hideInst(d)
        if d:IsA("BasePart") or d:IsA("Decal") or d:IsA("Texture") then
            if savedCharacterTransparency[d] == nil then
                savedCharacterTransparency[d] = d.Transparency
            end
            pcall(function() d.Transparency = 1 end)
        end
    end

    for _, d in ipairs(char:GetDescendants()) do
        hideInst(d)
    end

    morphHideConn = char.DescendantAdded:Connect(hideInst)
end

local function showCharacterAfterMorph()
    if morphHideConn then
        pcall(function() morphHideConn:Disconnect() end)
        morphHideConn = nil
    end
    for inst, saved in pairs(savedCharacterTransparency) do
        if inst and inst.Parent then
            pcall(function() inst.Transparency = saved end)
        end
    end
    savedCharacterTransparency = {}
end

----------------------------------------------------
-- LOCK
----------------------------------------------------
local function tryLockBoss(boss)
    lockedBoss = boss
    lockedBossRoot = nil
    lastFramePos = nil
    fpZoomOffset = 0
    fpUpOffset   = 0
    resetSmoothing()
    if boss then
        lastKnownBossName = boss.Name
        if boss.Parent then
            local info = bossInfo[boss]
            lockedBossRoot = (info and info.root) or getRoot(boss)
            if lockedBossRoot and lockedBossRoot.Parent then
                lastKnownBossPosition = lockedBossRoot.Position
                pushBossSnapshot(lastKnownBossPosition, os.clock())
            end
            computeEyeYOffset()
            refreshOrientCache()          -- ★ v9.5.2
            requestStreamAroundBoss(true)
        end
    else
        lastKnownBossName = "None"
        lastKnownBossPosition = nil
        cachedBossHead = nil
        cachedBossOrient = nil
    end
    __labelName, __labelStatus = nil, nil
end

local function findNextValidIndex(startIdx, step)
    local count = #bosses
    if count == 0 then return nil end
    local idx = startIdx
    for _ = 1, count do
        idx = ((idx - 1 + step) % count) + 1
        local b = bosses[idx]
        if b and b.Parent then
            local info = bossInfo[b]
            if info and info.root and info.root.Parent and not info.isStatic then
                return idx
            end
        end
    end
    return nil
end

local function switchBoss(step)
    if #bosses == 0 then setLabel("No bosses in list"); return end
    local startIdx = currentIndex
    if lockedBoss then
        for i, b in ipairs(bosses) do
            if b == lockedBoss then startIdx = i; break end
        end
    end
    local newIdx = findNextValidIndex(startIdx, step)
    if newIdx then
        currentIndex = newIdx
        tryLockBoss(bosses[newIdx])
    else
        setLabel("No other valid bosses")
    end
end

----------------------------------------------------
-- BOSS LIST UI
----------------------------------------------------
local function rebuildBossUI()
    for _, child in ipairs(scroll:GetChildren()) do
        if child:IsA("TextButton") then child:Destroy() end
    end
    for i, boss in ipairs(bosses) do
        local info = bossInfo[boss]
        if not (info and info.isStatic and boss ~= lockedBoss) then
            local reason = (info and info.reason) or "?"
            local btn = Instance.new("TextButton")
            btn.Size = UDim2.new(1, -10, 0, 30)
            btn.BackgroundColor3 = (boss == lockedBoss)
                and Color3.fromRGB(0, 120, 90) or Color3.fromRGB(60, 60, 60)
            btn.TextColor3 = Color3.new(1, 1, 1)
            btn.Font = Enum.Font.Gotham; btn.TextSize = 12
            btn.Text = boss.Name .. "  [" .. reason .. "]"
            btn.TextTruncate = Enum.TextTruncate.AtEnd
            btn.Parent = scroll
            Instance.new("UICorner", btn).CornerRadius = UDim.new(0, 6)
            local captureIdx, captureBoss = i, boss
            btn.MouseButton1Click:Connect(function()
                currentIndex = captureIdx
                tryLockBoss(captureBoss)
            end)
        end
    end
    task.defer(function()
        scroll.CanvasSize = UDim2.new(0, 0, 0, layout.AbsoluteContentSize.Y)
    end)
end

----------------------------------------------------
-- FULL SCAN
----------------------------------------------------
local function refreshBosses()
    local oldInfo = bossInfo
    local newBosses, newInfo = {}, {}
    local processed = 0

    for _, obj in ipairs(Workspace:GetDescendants()) do
        if obj:IsA("Model") then
            processed = processed + 1
            if processed % SCAN_YIELD_EVERY == 0 then task.wait() end

            local isB, reason, root, hasHum, hasAnim = classifyBoss(obj)
            if isB and root then
                local p = obj.Parent
                local nested = false
                while p and p ~= Workspace do
                    if newInfo[p] then nested = true; break end
                    p = p.Parent
                end
                if not nested then
                    table.insert(newBosses, obj)
                    local prev = oldInfo[obj]
                    local rootChanged = (not prev) or (prev.root ~= root)
                    if prev and not rootChanged then
                        newInfo[obj] = {
                            reason = reason,
                            root = root,
                            lastPos = prev.lastPos,
                            staticScans = prev.staticScans or 0,
                            isStatic = prev.isStatic or false,
                            hasHumanoid = hasHum or prev.hasHumanoid or false,
                            hasAnimCtrl = hasAnim or prev.hasAnimCtrl or false,
                        }
                    else
                        newInfo[obj] = {
                            reason = reason,
                            root = root,
                            lastPos = root.Position,
                            staticScans = 0,
                            isStatic = false,
                            hasHumanoid = hasHum,
                            hasAnimCtrl = hasAnim,
                        }
                    end
                end
            end
        end
    end

    bosses = newBosses
    bossInfo = newInfo

    local lockChanged = false
    if lockedBoss then
        local found = false
        for i, b in ipairs(bosses) do
            if b == lockedBoss then currentIndex = i; found = true; break end
        end
        if not found then
            local oldName = lockedBoss.Name
            for i, b in ipairs(bosses) do
                if b.Name == oldName then
                    lockedBoss = b
                    lockedBossRoot = bossInfo[b].root
                    currentIndex = i
                    found = true
                    lockChanged = true
                    break
                end
            end
            if not found then
                lockedBoss = nil
                lockedBossRoot = nil
                lockChanged = true
            end
        end
    end

    if lockChanged then
        cachedBossHead = nil
        cachedBossOrient = nil
        refreshOrientCache()
    end

    if #bosses > 0 then
        if currentIndex > #bosses then currentIndex = 1 end
        if currentIndex < 1 then currentIndex = #bosses end
        if not lockedBoss then
            tryLockBoss(bosses[currentIndex])
        end
    end

    rebuildBossUI()
    print(string.format("[BOSS] scan: %d bosses", #bosses))
end

----------------------------------------------------
-- MOVEMENT / ANTI-STATIC
----------------------------------------------------
local function checkBossMovement()
    local anyChanged = false
    for _, b in ipairs(bosses) do
        local info = bossInfo[b]
        if info and info.root and info.root.Parent then
            local curPos = info.root.Position
            if info.hasHumanoid or info.hasAnimCtrl then
                if info.isStatic then info.isStatic = false; anyChanged = true end
                info.staticScans = 0
                info.lastPos = curPos
            else
                if info.lastPos then
                    local moved = (curPos - info.lastPos).Magnitude
                    if moved > STATIC_MOVEMENT_THRESHOLD then
                        if info.isStatic then anyChanged = true end
                        info.staticScans = 0
                        info.isStatic = false
                    else
                        info.staticScans = (info.staticScans or 0) + 1
                        if info.staticScans >= STATIC_SCANS_LIMIT and not info.isStatic then
                            info.isStatic = true
                            anyChanged = true
                        end
                    end
                else
                    info.staticScans = 0
                    info.isStatic = false
                end
                info.lastPos = curPos
            end
        end
    end
    if anyChanged then rebuildBossUI() end
end

----------------------------------------------------
-- INCREMENTAL
----------------------------------------------------
local pendingNew, pendingFlag = {}, false
local CONTAINER_HINTS = {"enem","boss","mob","npc","spawn","wave","monster","entity","raid"}

local function isLikelyEnemyParent(p)
    if not p or p == Workspace then return true end
    for _ = 1, 3 do
        if not p or p == Workspace then return true end
        local pname = string.lower(p.Name)
        for _, hint in ipairs(CONTAINER_HINTS) do
            if string.find(pname, hint, 1, true) then return true end
        end
        p = p.Parent
    end
    return false
end

local function addIncremental(inst)
    for _, b in ipairs(bosses) do
        if b == inst then return end
    end
    local ok, isB, reason, root, hasHum, hasAnim = pcall(classifyBoss, inst)
    if ok and isB and root then
        table.insert(bosses, inst)
        bossInfo[inst] = {
            reason = reason or "?",
            root = root,
            lastPos = root.Position,
            staticScans = 0,
            isStatic = false,
            hasHumanoid = hasHum or false,
            hasAnimCtrl = hasAnim or false,
        }
        rebuildBossUI()
        if not lockedBoss then
            currentIndex = 1
            tryLockBoss(inst)
        end
    end
end

Workspace.DescendantAdded:Connect(function(inst)
    if not inst:IsA("Model") then return end
    if inst:GetAttribute("__BossSpectatorMorph") then return end
    if not isLikelyEnemyParent(inst.Parent) then return end
    table.insert(pendingNew, inst)
    if not pendingFlag then
        pendingFlag = true
        task.delay(INCREMENTAL_DELAY, function()
            pendingFlag = false
            local list = pendingNew; pendingNew = {}
            for _, c in ipairs(list) do
                if c and c.Parent then
                    pcall(addIncremental, c)
                end
            end
        end)
    end
end)

----------------------------------------------------
-- MOUSE STATE
----------------------------------------------------
local function targetMouseBehavior()
    if MOUSE_LOCK_MODE == "LockCurrentPosition" then
        return Enum.MouseBehavior.LockCurrentPosition
    elseif MOUSE_LOCK_MODE == "Default" then
        return Enum.MouseBehavior.Default
    end
    return Enum.MouseBehavior.LockCenter
end

local function updateMouseCapture()
    if spectating or freecam or thirdPerson then
        local tb = targetMouseBehavior()
        if UIS.MouseBehavior ~= tb then UIS.MouseBehavior = tb end
        if MOUSE_LOCK_MODE ~= "Default" then
            if UIS.MouseIconEnabled then UIS.MouseIconEnabled = false end
        else
            if not UIS.MouseIconEnabled then UIS.MouseIconEnabled = true end
        end
    else
        if UIS.MouseBehavior ~= Enum.MouseBehavior.Default then
            UIS.MouseBehavior = Enum.MouseBehavior.Default
        end
        if not UIS.MouseIconEnabled then UIS.MouseIconEnabled = true end
    end
end

local function markCamDirty()
    camDirty = true
    lastFramePos = nil
end

local function applyWheelDelta(sd)
    if not (spectating or freecam or thirdPerson) then return end
    if thirdPerson and not spectating and not freecam then
        if sd > 0 then tpDistance = math.clamp(tpDistance - 1, TP_MIN, TP_MAX)
        elseif sd < 0 then tpDistance = math.clamp(tpDistance + 1, TP_MIN, TP_MAX) end
        return
    end
    if firstPerson then
        if sd > 0 then
            fpZoomOffset = math.clamp(fpZoomOffset + FP_ZOOM_STEP, FP_ZOOM_MIN, FP_ZOOM_MAX)
        elseif sd < 0 then
            fpZoomOffset = math.clamp(fpZoomOffset - FP_ZOOM_STEP, FP_ZOOM_MIN, FP_ZOOM_MAX)
        end
        lastFramePos = nil
        return
    end
    local step = 1.5
    if sd > 0 then distance = math.clamp(distance - step, MIN_DISTANCE, MAX_DISTANCE)
    elseif sd < 0 then distance = math.clamp(distance + step, MIN_DISTANCE, MAX_DISTANCE) end
    markCamDirty()
end

UIS.InputChanged:Connect(function(input)
    if input.UserInputType == Enum.UserInputType.MouseWheel then
        applyWheelDelta(input.Position.Z)
        return
    end
    if input.UserInputType ~= Enum.UserInputType.MouseMovement then return end
    if isRightMouseDown then
        if input.Delta.X ~= 0 or input.Delta.Y ~= 0 then
            accMouseDx = accMouseDx + input.Delta.X
            accMouseDy = accMouseDy + input.Delta.Y
        end
        local mx, my = input.Position.X, input.Position.Y
        if lastMouseX and lastMouseY then
            local px, py = mx - lastMouseX, my - lastMouseY
            if px ~= 0 or py ~= 0 then
                accMouseDx = accMouseDx + px
                accMouseDy = accMouseDy + py
            end
        end
        lastMouseX, lastMouseY = mx, my
    else
        lastMouseX, lastMouseY = nil, nil
    end
end)

----------------------------------------------------
-- LIGHT
----------------------------------------------------
local function toggleLight()
    lightEnabled = not lightEnabled
    if lightEnabled then
        if not lightPart then
            lightPart = Instance.new("Part")
            lightPart.Name = "BossSpectatorLight"
            lightPart.Size = Vector3.new(0.5, 0.5, 0.5)
            lightPart.Anchored = true; lightPart.CanCollide = false
            lightPart.Transparency = 1; lightPart.Parent = workspace
            local pl = Instance.new("PointLight")
            pl.Parent = lightPart; pl.Brightness = 0.8; pl.Range = 300
            pl.Color = Color3.new(1, 1, 1)
        end
        lightPart.Parent = workspace
    else
        if lightPart then lightPart:Destroy(); lightPart = nil end
    end
end

local function setLightMode(mode)
    if lightMode ~= "none" and savedLightingState then
        Lighting.Ambient              = savedLightingState.Ambient
        Lighting.OutdoorAmbient       = savedLightingState.OutdoorAmbient
        Lighting.Brightness           = savedLightingState.Brightness
        Lighting.FogEnd               = savedLightingState.FogEnd
        Lighting.FogStart             = savedLightingState.FogStart
        Lighting.GlobalShadows        = savedLightingState.GlobalShadows
        Lighting.EnvironmentDiffuseScale  = savedLightingState.EnvironmentDiffuseScale
        Lighting.EnvironmentSpecularScale = savedLightingState.EnvironmentSpecularScale
        Lighting.ExposureCompensation = savedLightingState.ExposureCompensation
    end
    if superLightPart then superLightPart:Destroy(); superLightPart = nil end

    lightMode = mode

    if mode == "none" then
        savedLightingState = nil
        setLabel("LIGHT MODE: OFF")
        return
    end

    savedLightingState = {
        Ambient              = Lighting.Ambient,
        OutdoorAmbient       = Lighting.OutdoorAmbient,
        Brightness           = Lighting.Brightness,
        FogEnd               = Lighting.FogEnd,
        FogStart             = Lighting.FogStart,
        GlobalShadows        = Lighting.GlobalShadows,
        EnvironmentDiffuseScale  = Lighting.EnvironmentDiffuseScale,
        EnvironmentSpecularScale = Lighting.EnvironmentSpecularScale,
        ExposureCompensation = Lighting.ExposureCompensation,
    }

    if mode == "super" then
        superLightPart = Instance.new("Part")
        superLightPart.Name = "BossSpectatorSuperLight"
        superLightPart.Size = Vector3.new(0.5, 0.5, 0.5)
        superLightPart.Anchored = true; superLightPart.CanCollide = false
        superLightPart.Transparency = 1; superLightPart.Parent = workspace
        local pl = Instance.new("PointLight")
        pl.Parent = superLightPart; pl.Brightness = 5; pl.Range = 1000
        pl.Color = Color3.new(1, 1, 1)

        Lighting.Ambient             = Color3.new(1, 1, 1)
        Lighting.OutdoorAmbient      = Color3.new(1, 1, 1)
        Lighting.Brightness          = 5
        Lighting.FogEnd              = 100000
        Lighting.FogStart            = 100000
        Lighting.GlobalShadows       = false
        Lighting.EnvironmentDiffuseScale  = 1
        Lighting.EnvironmentSpecularScale = 1
        setLabel("SUPER LIGHT ON (F6)")

    elseif mode == "dim" then
        Lighting.Brightness           = savedLightingState.Brightness * DIM_BRIGHTNESS_MUL
        Lighting.Ambient              = savedLightingState.Ambient * DIM_AMBIENT_MUL
        Lighting.OutdoorAmbient       = savedLightingState.OutdoorAmbient * DIM_OUTDOOR_MUL
        Lighting.ExposureCompensation = (savedLightingState.ExposureCompensation or 0) + DIM_EXPOSURE_DELTA
        setLabel("DIM ON (F7)")
    end
end

local function toggleSuperLight()
    if lightMode == "super" then setLightMode("none")
    else setLightMode("super") end
end

local function toggleDimLight()
    if lightMode == "dim" then setLightMode("none")
    else setLightMode("dim") end
end

----------------------------------------------------
-- HIDE OTHER UI
----------------------------------------------------
local function hideAllOtherGuis()
    hiddenGuis = {}
    for _, child in ipairs(playerGui:GetChildren()) do
        if child:IsA("ScreenGui") and child ~= gui and child.Enabled then
            child.Enabled = false; table.insert(hiddenGuis, child)
        end
    end
    pcall(function() StarterGui:SetCoreGuiEnabled(Enum.CoreGuiType.All, false) end)
    pcall(function() StarterGui:SetCore("TopbarEnabled", false) end)
end

local function restoreAllGuis()
    for _, g in ipairs(hiddenGuis) do
        if g and g.Parent then pcall(function() g.Enabled = true end) end
    end
    hiddenGuis = {}
    pcall(function() StarterGui:SetCoreGuiEnabled(Enum.CoreGuiType.All, true) end)
    pcall(function() StarterGui:SetCore("TopbarEnabled", true) end)
end

local function toggleHideOtherUI()
    hideOtherUI = not hideOtherUI
    if hideOtherUI then hideAllOtherGuis(); setLabel("UI HIDDEN (F2)")
    else restoreAllGuis(); setLabel("UI RESTORED (F2)") end
end

playerGui.ChildAdded:Connect(function(child)
    if hideOtherUI and child:IsA("ScreenGui") and child ~= gui then
        task.defer(function()
            if hideOtherUI and child and child.Parent then
                child.Enabled = false
                if not table.find(hiddenGuis, child) then table.insert(hiddenGuis, child) end
            end
        end)
    end
end)

----------------------------------------------------
-- SPRINT / BOOST
----------------------------------------------------
local function applySprintToCharacter()
    local char = player.Character
    if not char then return end
    local hum = char:FindFirstChildWhichIsA("Humanoid")
    if not hum then return end
    if originalWalkSpeed == nil then originalWalkSpeed = hum.WalkSpeed end
    hum.WalkSpeed = sprintEnabled and SPRINT_SPEED or originalWalkSpeed
end

local function toggleSprint()
    sprintEnabled = not sprintEnabled
    applySprintToCharacter()
    setLabel(sprintEnabled and ("SPRINT ON (" .. SPRINT_SPEED .. ")") or "SPRINT OFF")
end

local function toggleFreecamBoost()
    freecamBoost = not freecamBoost
end

----------------------------------------------------
-- CAMERA RESTORE
----------------------------------------------------
local function restorePlayerCamera()
    local char = player.Character
    if not char then return end
    local hum = char:FindFirstChildWhichIsA("Humanoid")
    if not hum or not hum.Parent then return end
    if camera.CameraSubject ~= hum then pcall(function() camera.CameraSubject = hum end) end
    if camera.CameraType ~= Enum.CameraType.Custom then
        pcall(function() camera.CameraType = Enum.CameraType.Custom end)
    end
    pcall(function()
        if player.CameraMinZoomDistance ~= 0.5 then player.CameraMinZoomDistance = 0.5 end
        if player.CameraMaxZoomDistance ~= 128 then player.CameraMaxZoomDistance = 128 end
    end)
    pcall(function()
        UIS.MouseBehavior = Enum.MouseBehavior.Default
        UIS.MouseIconEnabled = true
    end)
    lastFramePos = nil
end

local function syncYawPitchFromCamera()
    local look = camera.CFrame.LookVector
    pitch = math.clamp(math.asin(math.clamp(look.Y, -1, 1)), -1.2, 1.2)
    yaw = math.atan2(-look.X, -look.Z)
    markCamDirty()
end

----------------------------------------------------
-- MORPH (F1) — toggle visual morph, PERSISTS
----------------------------------------------------
local function clearMorph()
    if morphModel then
        pcall(function() morphModel:Destroy() end)
        morphModel = nil
    end
    showCharacterAfterMorph()
    morphedBossName = nil
end

local function doMorph()
    if morphModel then
        clearMorph()
        setLabel("MORPH OFF (F1)")
        print("[BOSS] morph cleared")
        return
    end

    if not lockedBoss then
        setLabel("MORPH: no boss locked (use O/P)")
        return
    end
    if not lockedBoss.Parent then
        setLabel("MORPH: boss not in workspace")
        return
    end

    local char = player.Character
    local playerHRP = char and char:FindFirstChild("HumanoidRootPart")
    if not playerHRP then
        setLabel("MORPH: no character")
        return
    end

    local bossName = lockedBoss.Name

    local clone
    local okClone, cloneErr = pcall(function()
        clone = lockedBoss:Clone()
    end)
    if not okClone or not clone then
        setLabel("MORPH: clone failed (Archivable?)")
        warn("[BOSS] morph clone error: " .. tostring(cloneErr))
        return
    end

    pcall(function() clone:SetAttribute("__BossSpectatorMorph", true) end)
    clone.Name = "__BossSpectatorMorph"

    for _, d in ipairs(clone:GetDescendants()) do
        if d:IsA("Script") or d:IsA("LocalScript") or d:IsA("ModuleScript")
           or d:IsA("Humanoid") or d:IsA("AnimationController") or d:IsA("Animator")
           or d:IsA("Tool") then
            d:Destroy()
        end
    end

    for _, d in ipairs(clone:GetDescendants()) do
        if d:IsA("BasePart") then
            d.Anchored = true
            d.CanCollide = false
            d.CanQuery = false
            d.CanTouch = false
            d.Massless = true
        end
    end

    local clonedRoot = getRoot(clone)
    if not clonedRoot then
        setLabel("MORPH: no root part in clone")
        clone:Destroy()
        return
    end
    clone.PrimaryPart = clonedRoot

    clone.Parent = workspace
    local targetCF = playerHRP.CFrame * CFrame.new(0, MORPH_Y_OFFSET, 0)
    pcall(function() clone:PivotTo(targetCF) end)

    morphModel = clone
    morphedBossName = bossName

    hideCharacterForMorph(char)

    setLabel("MORPH: " .. bossName .. " (F1 to undo)")
    print("[BOSS] morphed into: " .. bossName)
end

----------------------------------------------------
-- DELTA READER
----------------------------------------------------
RunService.RenderStepped:Connect(function()
    if not (spectating or freecam or thirdPerson) then
        rotationDeltaX, rotationDeltaY = 0, 0
        accMouseDx, accMouseDy = 0, 0
        return
    end

    local tb = targetMouseBehavior()
    if UIS.MouseBehavior ~= tb then UIS.MouseBehavior = tb end

    local md = UIS:GetMouseDelta()
    if md.X ~= 0 or md.Y ~= 0 then
        rotationDeltaX, rotationDeltaY = md.X, md.Y
    elseif accMouseDx ~= 0 or accMouseDy ~= 0 then
        rotationDeltaX, rotationDeltaY = accMouseDx, accMouseDy
    else
        rotationDeltaX, rotationDeltaY = 0, 0
    end
    accMouseDx, accMouseDy = 0, 0
end)

----------------------------------------------------
-- MORPH FOLLOW (persists through respawn)
----------------------------------------------------
RunService.RenderStepped:Connect(function()
    if not morphModel then return end
    local char = player.Character
    if not char then return end
    local hrp = char:FindFirstChild("HumanoidRootPart")
    if not hrp then return end
    local targetCF = hrp.CFrame * CFrame.new(0, MORPH_Y_OFFSET, 0)
    pcall(function() morphModel:PivotTo(targetCF) end)
end)

----------------------------------------------------
-- CAMERA APPLIER
----------------------------------------------------
local function autoLockFirst()
    if lockedBoss then return end
    if #bosses == 0 then return end
    if currentIndex > #bosses then currentIndex = 1 end
    if currentIndex < 1 then currentIndex = #bosses end
    local b = bosses[currentIndex]
    if b and b.Parent then tryLockBoss(b) end
end

local function syncYawToBoss()
    if not lockedBoss or not lockedBoss.Parent then return end
    local orient = getBossOrient() or lockedBossRoot
    if orient and orient:IsA("BasePart") and orient.Parent then
        local look = orient.CFrame.LookVector
        local horiz = Vector3.new(look.X, 0, look.Z)
        if horiz.Magnitude > 0.0001 then
            yaw = math.atan2(-horiz.X, -horiz.Z)
            camDirty = true
            lastFramePos = nil
        end
    end
end

pcall(function() RunService:UnbindFromRenderStep("BossSpectatorOverride") end)

RunService:BindToRenderStep("BossSpectatorOverride", Enum.RenderPriority.Camera.Value + 1, function(dt)
    if not (spectating or freecam or thirdPerson) then return end

    if camera.CameraType ~= Enum.CameraType.Scriptable then
        camera.CameraType = Enum.CameraType.Scriptable
    end

    if isRightMouseDown and (rotationDeltaX ~= 0 or rotationDeltaY ~= 0) then
        yaw   = yaw   - rotationDeltaX * SENSITIVITY
        pitch = math.clamp(pitch - rotationDeltaY * SENSITIVITY, -1.2, 1.2)
        camDirty = true
        lastFramePos = nil
    end

    if spectating then
        autoLockFirst()
        if not lockedBoss then setLabel("No boss - O/P"); return end

        local root = lockedBossRoot
        if not root or not root.Parent then
            local info = bossInfo[lockedBoss]
            root = (info and info.root) or getRoot(lockedBoss)
            lockedBossRoot = root
            if info then info.root = root end
            cachedBossOrient = root
            lastFramePos = nil
        end

        if root and root.Parent then
            lastKnownBossPosition = root.Position
        end
        if not lastKnownBossPosition then
            setLabel("Waiting for boss... (O/P)"); return
        end

        requestStreamAroundBoss()

        local now = os.clock()
        pushBossSnapshot(lastKnownBossPosition, now)
        local sampledPos = sampleBossSnapshot(now, lastKnownBossPosition)

        -- ★ v9.5.2: use cached reference instead of per-frame recursive FindFirstChild
        local orientPart = getBossOrient()

        if followBossRotation and orientPart and orientPart.Parent and not isRightMouseDown then
            local look = orientPart.CFrame.LookVector
            local horiz = Vector3.new(look.X, 0, look.Z)
            if horiz.Magnitude > 0.0001 then
                local targetYaw = math.atan2(-horiz.X, -horiz.Z)
                local diff = math.atan2(math.sin(targetYaw - yaw), math.cos(targetYaw - yaw))
                if math.abs(diff) > 0.0001 then
                    yaw = yaw + diff * math.min(1, dt * FOLLOW_ROT_SPEED)
                    camDirty = true
                end
            end
        end

        if firstPerson then
            if camDirty then
                cachedRot = CFrame.Angles(0, yaw, 0) * CFrame.Angles(pitch, 0, 0)
                camDirty = false
            end

            local raiseKey = UIS:IsKeyDown(Enum.KeyCode.Space)
            local lowerKey = UIS:IsKeyDown(Enum.KeyCode.LeftShift)
                              or UIS:IsKeyDown(Enum.KeyCode.RightShift)
            if raiseKey then
                fpUpOffset = math.clamp(fpUpOffset + FP_UP_SPEED * dt, FP_UP_MIN, FP_UP_MAX)
            end
            if lowerKey then
                fpUpOffset = math.clamp(fpUpOffset - FP_UP_SPEED * dt, FP_UP_MIN, FP_UP_MAX)
            end

            local offsetY = eyeYOffset or FP_EYE_HEIGHT
            local baseEyePos = sampledPos + Vector3.new(0, offsetY, 0)

            -- ★ v9.5.2: cached orient (no FindFirstChild per frame)
            local orientBase = orientPart

            local bossForward = Vector3.new(0, 0, 0)
            if orientBase then
                local look = orientBase.CFrame.LookVector
                local horiz = Vector3.new(look.X, 0, look.Z)
                if horiz.Magnitude > 0.001 then
                    bossForward = horiz.Unit
                end
            end

            local eyePos = baseEyePos
                + bossForward * fpZoomOffset
                + Vector3.new(0, fpUpOffset, 0)

            if camera and camera.Parent then
                camera.CFrame = CFrame.new(eyePos) * cachedRot
                lastFramePos = eyePos
            end

            local nm = lastKnownBossName
            local rotTag = followBossRotation and " ROT" or ""
            local status = string.format(" [FP z:%.1f h:%.1f%s]", fpZoomOffset, fpUpOffset, rotTag)
            if status ~= __labelStatus or nm ~= __labelName then
                __labelStatus, __labelName = status, nm
                setLabel("Current: " .. nm .. status)
            end
            return
        end

        if camDirty then
            cachedRot = CFrame.Angles(0, yaw, 0) * CFrame.Angles(pitch, 0, 0)
            cachedOffset = cachedRot * Vector3.new(0, 0, distance)
            camDirty = false
        end

        local target = sampledPos + HEIGHT_OFFSET_V
        local camPos = target + cachedOffset

        if camera and camera.Parent then
            camera.CFrame = CFrame.new(camPos) * cachedRot
            lastFramePos = camPos
        end

        local status = (lockedBoss.Parent and " [LOCK]" or " [HELD]")
                     .. (followBossRotation and " [ROT]" or "")
        local nm = lastKnownBossName
        if status ~= __labelStatus or nm ~= __labelName then
            __labelStatus, __labelName = status, nm
            setLabel("Current: " .. nm .. status)
        end

    elseif freecam then
        if not freecamPosition then freecamPosition = camera.CFrame.Position end

        local speed = freecamBoost and FREECAM_BOOST_SPEED or FREECAM_SPEED
        local move = Vector3.new()
        local forward = camera.CFrame.LookVector
        local right = camera.CFrame.RightVector
        if UIS:IsKeyDown(Enum.KeyCode.T) then move = move + forward end
        if UIS:IsKeyDown(Enum.KeyCode.G) then move = move - forward end
        if UIS:IsKeyDown(Enum.KeyCode.F) then move = move - right end
        if UIS:IsKeyDown(Enum.KeyCode.H) then move = move + right end
        if UIS:IsKeyDown(Enum.KeyCode.Space) then move = move + Vector3.new(0,1,0) end
        if UIS:IsKeyDown(Enum.KeyCode.LeftShift) or UIS:IsKeyDown(Enum.KeyCode.RightShift) then
            move = move - Vector3.new(0,1,0)
        end
        if move.Magnitude > 0 then
            freecamPosition = freecamPosition + move.Unit * speed * dt
            lastFramePos = nil
        end

        if camDirty then
            cachedRot = CFrame.Angles(0, yaw, 0) * CFrame.Angles(pitch, 0, 0)
            camDirty = false
        end
        if camera and camera.Parent then
            camera.CFrame = CFrame.new(freecamPosition) * cachedRot
        end
        setLabel("Freecam mode" .. (freecamBoost and " [BOOST]" or ""))

    elseif thirdPerson then
        local char = player.Character
        if char then
            for _, part in ipairs(char:GetDescendants()) do
                if part:IsA("BasePart") and part.LocalTransparencyModifier ~= 0 then
                    part.LocalTransparencyModifier = 0
                end
            end

            local hum  = char:FindFirstChildWhichIsA("Humanoid")
            local head = char:FindFirstChild("Head")
            local root = char:FindFirstChild("HumanoidRootPart")
            if hum and hum.Parent and (head or root) then
                if not isRightMouseDown and root and hum.MoveDirection.Magnitude > 0.1 then
                    local look = root.CFrame.LookVector
                    local targetYaw = math.atan2(-look.X, -look.Z)
                    local diff = math.atan2(math.sin(targetYaw - yaw), math.cos(targetYaw - yaw))
                    if math.abs(diff) > 0.001 then
                        yaw = yaw + diff * math.min(1, dt * TP_YAW_FOLLOW_SPEED)
                        camDirty = true
                    end
                end

                if camDirty then
                    cachedRot = CFrame.Angles(0, yaw, 0) * CFrame.Angles(pitch, 0, 0)
                    camDirty = false
                end
                local basePos = (head and head.Position) or root.Position
                local target = basePos + Vector3.new(0, 0.5, 0)
                local offset = cachedRot * Vector3.new(0, 0, tpDistance)
                local camPos = target + offset
                if camera and camera.Parent then
                    camera.CFrame = CFrame.new(camPos) * cachedRot
                end
            end
        end
        setLabel("Third-Person (V - exit)")
    end
end)

----------------------------------------------------
-- TP
----------------------------------------------------
local function teleportPlayerToFreecam()
    if not freecam or not freecamPosition then return end
    local character = player.Character
    if not character then return end
    local rootPart = character:FindFirstChild("HumanoidRootPart")
    if not rootPart then return end
    rootPart.CFrame = CFrame.new(freecamPosition + Vector3.new(0, 2, 0))
    freecam = false; freecamPosition = nil
    task.defer(restorePlayerCamera)
    updateMouseCapture()
    setLabel("Teleported (freecam OFF)")
end

----------------------------------------------------
-- GOD MODE
----------------------------------------------------
local function clearGodModeConns()
    for _, c in ipairs(godModeConns) do
        pcall(function() c:Disconnect() end)
    end
    godModeConns = {}
end

local function setGodHealth(hum)
    if not hum or not hum.Parent then return end
    pcall(function()
        if hum.MaxHealth < GOD_HEALTH then hum.MaxHealth = GOD_HEALTH end
    end)
    pcall(function()
        if hum.Health < hum.MaxHealth then hum.Health = hum.MaxHealth end
    end)
end

local function killDeathAnimations(char)
    if not char then return end
    pcall(function()
        local hum = char:FindFirstChildWhichIsA("Humanoid")
        if hum then
            local animator = hum:FindFirstChildWhichIsA("Animator")
            if animator then
                for _, track in ipairs(animator:GetPlayingAnimationTracks()) do
                    local name = track.Name
                    if name then
                        local ln = string.lower(name)
                        if string.find(ln, "death", 1, true)
                           or string.find(ln, "dead", 1, true)
                           or string.find(ln, "die", 1, true) then
                            pcall(function() track:Stop(0) end)
                        end
                    end
                end
            end
        end
    end)
end

local function installGodModeGuards(char)
    if not char then return end
    godModeLastChar = char
    clearGodModeConns()

    local hum = char:FindFirstChildWhichIsA("Humanoid")
    if not hum then return end

    setGodHealth(hum)

    table.insert(godModeConns, hum.HealthChanged:Connect(function()
        if not godMode then return end
        if hum.Health < hum.MaxHealth then
            hum.Health = hum.MaxHealth
        end
    end))

    table.insert(godModeConns, hum:GetPropertyChangedSignal("MaxHealth"):Connect(function()
        if godMode then setGodHealth(hum) end
    end))

    table.insert(godModeConns, hum.Died:Connect(function()
        if not godMode then return end
        task.defer(function()
            if not godMode or not hum.Parent then return end
            setGodHealth(hum)
            pcall(function() hum:ChangeState(Enum.HumanoidStateType.Running) end)
            killDeathAnimations(char)
            local cam = workspace.CurrentCamera
            if cam then pcall(function() cam.CameraSubject = hum end) end
        end)
    end))
end

RunService.RenderStepped:Connect(function()
    if not godMode then return end
    local char = player.Character
    if not char then return end
    local hum = char:FindFirstChildWhichIsA("Humanoid")
    if hum and (hum.Health < hum.MaxHealth or hum.MaxHealth < GOD_HEALTH) then
        setGodHealth(hum)
    end
end)

RunService.Stepped:Connect(function()
    if not godMode then return end
    local char = player.Character
    if not char then return end
    local hum = char:FindFirstChildWhichIsA("Humanoid")
    if hum and (hum.Health < hum.MaxHealth or hum.MaxHealth < GOD_HEALTH) then
        setGodHealth(hum)
    end
end)

RunService.Heartbeat:Connect(function()
    if not godMode then return end
    local char = player.Character
    if not char then return end
    local hum = char:FindFirstChildWhichIsA("Humanoid")
    if hum then
        if hum.Health < hum.MaxHealth or hum.MaxHealth < GOD_HEALTH then
            setGodHealth(hum)
        end
        if hum:GetState() == Enum.HumanoidStateType.Dead then
            pcall(function() hum:ChangeState(Enum.HumanoidStateType.Running) end)
            killDeathAnimations(char)
        end
    end
end)

local function toggleGodMode()
    local character = player.Character
    if not character then return end
    local humanoid = character:FindFirstChildWhichIsA("Humanoid")
    if not humanoid then return end

    godMode = not godMode

    if godMode then
        installGodModeGuards(character)
        setLabel("GOD MODE ON — INSTANT HP RESTORE (N)")
    else
        clearGodModeConns()
        godModeLastChar = nil
        pcall(function() humanoid.MaxHealth = 100 end)
        pcall(function() humanoid.Health = 100 end)
        setLabel("GOD MODE OFF (N)")
    end
end

----------------------------------------------------
-- FOLLOW BOSS ROTATION TOGGLE
----------------------------------------------------
local function toggleFollowBossRotation()
    followBossRotation = not followBossRotation
    if followBossRotation then
        syncYawToBoss()
        setLabel("FOLLOW BOSS ROTATION: ON (J)")
    else
        setLabel("FOLLOW BOSS ROTATION: OFF (J)")
    end
end

----------------------------------------------------
-- UNIFIED INPUT
----------------------------------------------------
UIS.InputBegan:Connect(function(input, gameProcessed)
    if input.UserInputType == Enum.UserInputType.MouseButton2 then
        isRightMouseDown = true
        lastMouseX, lastMouseY = nil, nil
        return
    end

    if input.UserInputType == Enum.UserInputType.MouseWheel then
        applyWheelDelta(input.Position.Z)
        return
    end

    if input.KeyCode == Enum.KeyCode.W then
        if UIS:GetFocusedTextBox() then return end
        local now = tick()
        if now - lastWTime <= DOUBLE_TAP_TIME then
            toggleSprint(); lastWTime = 0
        else
            lastWTime = now
        end
        return
    end
    if input.KeyCode == Enum.KeyCode.T then
        if UIS:GetFocusedTextBox() then return end
        local now2 = tick()
        if now2 - lastTTime <= DOUBLE_TAP_TIME then
            toggleFreecamBoost(); lastTTime = 0
        else
            lastTTime = now2
        end
        return
    end

    if gameProcessed then return end
    if UIS:GetFocusedTextBox() then return end

    local kc = input.KeyCode
    if kc == Enum.KeyCode.Q then
        spectating = not spectating
        if spectating then
            if freecam then freecam = false; freecamPosition = nil end
            if thirdPerson then thirdPerson = false end
        else
            firstPerson = false
            task.defer(restorePlayerCamera)
        end
        lastFramePos = nil; updateMouseCapture()
        UIS:GetMouseDelta()

    elseif kc == Enum.KeyCode.I then
        firstPerson = not firstPerson
        if firstPerson then
            spectating = true
            if freecam then freecam = false; freecamPosition = nil end
            if thirdPerson then thirdPerson = false end
            fpZoomOffset = 0
            fpUpOffset   = 0
            resetSmoothing()
            computeEyeYOffset()
            refreshOrientCache()
            markCamDirty()
            lastFramePos = nil
            if followBossRotation then syncYawToBoss() end
            setLabel("FIRST-PERSON ON (I) — Wheel zoom, SPACE up, LShift down")
        else
            markCamDirty()
            lastFramePos = nil
            setLabel("FIRST-PERSON OFF (I)")
        end
        updateMouseCapture()

    elseif kc == Enum.KeyCode.O then switchBoss(1)
    elseif kc == Enum.KeyCode.P then switchBoss(-1)

    elseif kc == Enum.KeyCode.M then
        freecam = not freecam
        if freecam then
            firstPerson = false
            freecamPosition = camera.CFrame.Position
            syncYawPitchFromCamera()
            if spectating then spectating = false end
            if thirdPerson then thirdPerson = false end
        else
            freecamPosition = nil; task.defer(restorePlayerCamera)
        end
        lastFramePos = nil; updateMouseCapture()

    elseif kc == Enum.KeyCode.V then
        thirdPerson = not thirdPerson
        if thirdPerson then
            firstPerson = false
            if spectating then spectating = false end
            if freecam then freecam = false; freecamPosition = nil end
            local char = player.Character
            local root = char and char:FindFirstChild("HumanoidRootPart")
            if root then
                local look = root.CFrame.LookVector
                yaw = math.atan2(-look.X, -look.Z)
            else
                yaw = 0
            end
            pitch = 0
            markCamDirty()
        else
            task.defer(restorePlayerCamera)
        end
        lastFramePos = nil; updateMouseCapture()

    elseif kc == Enum.KeyCode.K then
        uiVisible = not uiVisible
        mainFrame.Visible = uiVisible

    elseif kc == Enum.KeyCode.L then teleportPlayerToFreecam()
    elseif kc == Enum.KeyCode.N then toggleGodMode()
    elseif kc == Enum.KeyCode.J then toggleFollowBossRotation()
    elseif kc == Enum.KeyCode.F1 then doMorph()
    elseif kc == Enum.KeyCode.F5 then toggleLight()
    elseif kc == Enum.KeyCode.F6 then toggleSuperLight()
    elseif kc == Enum.KeyCode.F7 then toggleDimLight()
    elseif kc == Enum.KeyCode.F2 then toggleHideOtherUI()

    elseif kc == Enum.KeyCode.R then
        spectating = false
        firstPerson = false
        freecam = false; freecamPosition = nil
        thirdPerson = false
        fpZoomOffset = 0
        fpUpOffset   = 0
        resetSmoothing()
        restorePlayerCamera()
        updateMouseCapture()
        setLabel("Camera HARD RESET (R)")
    end
end)

UIS.InputEnded:Connect(function(input)
    if input.UserInputType == Enum.UserInputType.MouseButton2 then
        isRightMouseDown = false
        lastMouseX, lastMouseY = nil, nil
    end
end)

----------------------------------------------------
-- HEARTBEAT
----------------------------------------------------
local lastModeKey = nil
local hideTick = 0
local orientRefreshTick = 0

local function currentModeKey()
    return (spectating and "S" or "") .. (firstPerson and "P" or "") .. (freecam and "F" or "") .. (thirdPerson and "V" or "")
end

RunService.Heartbeat:Connect(function(dt)
    if lightEnabled and lightPart then lightPart.Position = camera.CFrame.Position end
    if lightMode == "super" and superLightPart then superLightPart.Position = camera.CFrame.Position end

    if godMode then
        local char = player.Character
        if char then
            local hum = char:FindFirstChildWhichIsA("Humanoid")
            if hum then
                setGodHealth(hum)
                if hum:GetState() == Enum.HumanoidStateType.Dead then
                    pcall(function() hum:ChangeState(Enum.HumanoidStateType.Running) end)
                    killDeathAnimations(char)
                end
            end
        end
    end

    -- ★ v9.5.2: periodic orient cache refresh (only when invalid)
    orientRefreshTick = orientRefreshTick + dt
    if orientRefreshTick >= 2.0 then
        orientRefreshTick = 0
        if lockedBoss and lockedBoss.Parent then
            if not cachedBossOrient or not cachedBossOrient.Parent then
                refreshOrientCache()
            end
        end
    end

    local k = currentModeKey()
    if k ~= lastModeKey then
        lastModeKey = k
        lastFramePos = nil
        resetSmoothing()
        updateMouseCapture()
    end

    hideTick = hideTick + dt
    if hideTick >= 0.5 then
        hideTick = 0
        if not spectating and not freecam and not thirdPerson then
            local char = player.Character
            local hum = char and char:FindFirstChildWhichIsA("Humanoid")
            if hum and hum.Parent then
                if camera.CameraSubject ~= hum then camera.CameraSubject = hum end
                if camera.CameraType ~= Enum.CameraType.Custom then
                    camera.CameraType = Enum.CameraType.Custom
                end
            end
        end
        if hideOtherUI then
            for _, child in ipairs(playerGui:GetChildren()) do
                if child:IsA("ScreenGui") and child ~= gui and child.Enabled then
                    child.Enabled = false
                    if not table.find(hiddenGuis, child) then table.insert(hiddenGuis, child) end
                end
            end
            pcall(function() StarterGui:SetCoreGuiEnabled(Enum.CoreGuiType.All, false) end)
        end
    end
end)

----------------------------------------------------
-- CURRENT CAMERA CHANGE
----------------------------------------------------
workspace:GetPropertyChangedSignal("CurrentCamera"):Connect(function()
    local newCam = workspace.CurrentCamera
    if newCam and newCam ~= camera then
        camera = newCam
        lastFramePos = nil
        task.wait()
        if not spectating and not freecam and not thirdPerson then
            restorePlayerCamera()
        end
    end
end)

----------------------------------------------------
-- RESPAWN (morph PERSISTS)
----------------------------------------------------
player.CharacterAdded:Connect(function(char)
    if morphModel then
        task.spawn(function()
            char:WaitForChild("Humanoid", 10)
            task.wait(0.05)
            if morphModel and player.Character == char then
                hideCharacterForMorph(char)
            end
        end)
    end

    lockedBossRoot = nil
    lastFramePos = nil
    resetSmoothing()
    cachedBossHead = nil
    cachedBossOrient = nil

    if godMode then
        task.spawn(function()
            char:WaitForChild("Humanoid", 10)
            task.wait(0.05)
            if godMode then installGodModeGuards(char) end
        end)
    end

    task.spawn(function()
        local hum = char:WaitForChild("Humanoid", 10)
        if hum and sprintEnabled then
            if originalWalkSpeed == nil then originalWalkSpeed = hum.WalkSpeed end
            hum.WalkSpeed = SPRINT_SPEED
        end
    end)

    if thirdPerson then
        task.spawn(function()
            char:WaitForChild("HumanoidRootPart", 10)
            task.wait(0.1)
            local root = char:FindFirstChild("HumanoidRootPart")
            if root and thirdPerson then
                local look = root.CFrame.LookVector
                yaw = math.atan2(-look.X, -look.Z)
                pitch = 0
                markCamDirty()
            end
        end)
        return
    end

    if spectating or freecam then return end
    task.spawn(function()
        char:WaitForChild("Humanoid", 10)
        task.wait(0.1)
        if not spectating and not freecam and not thirdPerson then
            restorePlayerCamera()
        end
    end)
end)

----------------------------------------------------
-- INIT
----------------------------------------------------
updateMouseCapture()
UIS:GetMouseDelta()

task.spawn(function()
    if not game:IsLoaded() then game.Loaded:Wait() end
    task.wait(1.5)
    local ok, err = pcall(refreshBosses)
    if not ok then
        warn("[BOSS] refreshBosses error: " .. tostring(err))
    end
end)

task.spawn(function()
    while true do
        task.wait(BOSS_REFRESH_INTERVAL)
        pcall(checkBossMovement)
        local ok, err = pcall(refreshBosses)
        if not ok then
            warn("[BOSS] periodic refresh error: " .. tostring(err))
        end
    end
end)

print("[BOSS] v9.5.2 fully loaded OK (anti-jitter + stream + PERSISTENT morph + LAG FIX)")