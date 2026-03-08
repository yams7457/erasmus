-- lib/samples.lua
-- Sample scanning, loading, triggering, and config parsing.

local Samples = {}

local SAMPLE_DIR = _path.audio .. "erasmus/"
local MAX_SAMPLES = 128
local AUDIO_EXTENSIONS = {wav=true, flac=true, aif=true, aiff=true}

-- Module-level references (set by init)
local S
local Snapshots

function Samples.init(state, snapshots)
  S = state
  Snapshots = snapshots
end

-- Get display name from filepath
local function display_name(filepath)
  local name = filepath:match("([^/]+)$") or filepath
  name = name:match("(.+)%..+$") or name
  return name
end

local function is_audio_file(name)
  local ext = name:match("%.([^%.]+)$")
  return ext and AUDIO_EXTENSIONS[ext:lower()]
end

-- Parse a config.txt file for per-sample overrides.
-- Format: one entry per line, "sample_name: rate=X amp=Y" (fields optional).
local function parse_sample_config(dir_path)
  local config = {}
  local f = io.open(dir_path .. "config.txt", "r")
  if not f then return config end
  for line in f:lines() do
    line = line:match("^%s*(.-)%s*$")
    if line ~= "" and not line:match("^#") then
      local name, rest = line:match("^([^:]+):%s*(.+)$")
      if name and rest then
        name = name:match("^%s*(.-)%s*$")
        local entry = {}
        for key, val in rest:gmatch("(%w+)%s*=%s*([%d%.%-]+)") do
          entry[key] = tonumber(val)
        end
        config[name] = entry
      end
    end
  end
  f:close()
  return config
end

local function collect_audio_files(dir_path)
  local files = {}
  local entries = util.scandir(dir_path)
  if not entries then return files end
  for _, entry in ipairs(entries) do
    if not entry:match("/$") and is_audio_file(entry) then
      table.insert(files, dir_path .. entry)
    end
  end
  table.sort(files)
  return files
end

-- Assign per-group brightness via greedy graph coloring.
local function compute_group_brightness(num_groups)
  S.group_brightness = {}
  if num_groups <= 1 then
    S.group_brightness[1] = 8
    return
  end

  local MIN_BRIGHT = 4
  local MAX_BRIGHT = 13

  local adj = {}
  for grp = 1, num_groups do adj[grp] = {} end
  local offsets = {{0, 1}, {0, -1}, {1, 0}, {-1, 0}}
  for idx = 1, S.num_samples do
    local s = S.samples[idx]
    local g1 = s.group_idx
    for _, off in ipairs(offsets) do
      local nr, nc = s.grid_row + off[1], s.grid_col + off[2]
      if S.grid_samples[nr] and S.grid_samples[nr][nc] then
        local g2 = S.samples[S.grid_samples[nr][nc]].group_idx
        if g1 ~= g2 then
          adj[g1][g2] = true
          adj[g2][g1] = true
        end
      end
    end
  end

  local order = {}
  for grp = 1, num_groups do order[grp] = grp end
  table.sort(order, function(a, b)
    local ca, cb = 0, 0
    for _ in pairs(adj[a]) do ca = ca + 1 end
    for _ in pairs(adj[b]) do cb = cb + 1 end
    return ca > cb
  end)

  local mid = math.floor((MIN_BRIGHT + MAX_BRIGHT) / 2)

  for _, grp in ipairs(order) do
    local neighbor_vals = {}
    for nb, _ in pairs(adj[grp]) do
      if S.group_brightness[nb] then
        table.insert(neighbor_vals, S.group_brightness[nb])
      end
    end

    if #neighbor_vals == 0 then
      S.group_brightness[grp] = mid
    else
      local best_val = mid
      local best_min_dist = -1
      for v = MIN_BRIGHT, MAX_BRIGHT do
        local min_dist = math.huge
        for _, nv in ipairs(neighbor_vals) do
          min_dist = math.min(min_dist, math.abs(v - nv))
        end
        if min_dist > best_min_dist
          or (min_dist == best_min_dist and math.abs(v - mid) < math.abs(best_val - mid)) then
          best_min_dist = min_dist
          best_val = v
        end
      end
      S.group_brightness[grp] = best_val
    end
  end
end

-- Scan sample directory and populate state.samples + state.grid_samples.
function Samples.scan()
  S.samples = {}
  S.num_samples = 0
  S.pad_amps = {}
  S.grid_samples = {}
  S.group_names = {}

  os.execute("mkdir -p " .. SAMPLE_DIR)

  local groups = {}

  local entries = util.scandir(SAMPLE_DIR)
  if not entries then
    print("erasmus: could not scan " .. SAMPLE_DIR)
    return
  end

  local root_files = {}
  local subdirs = {}
  for _, entry in ipairs(entries) do
    if entry:match("/$") then
      local dir_name = entry:match("^(.-)/$") or entry
      if dir_name ~= "snapshots" then
        table.insert(subdirs, entry)
      end
    elseif is_audio_file(entry) then
      table.insert(root_files, SAMPLE_DIR .. entry)
    end
  end

  table.sort(root_files)
  if #root_files > 0 then
    local root_config = parse_sample_config(SAMPLE_DIR)
    table.insert(groups, {name = "(root)", files = root_files, config = root_config})
  end

  table.sort(subdirs)
  for _, subdir in ipairs(subdirs) do
    local dir_name = subdir:match("^(.-)/$") or subdir
    local dir_path = SAMPLE_DIR .. subdir
    local dir_files = collect_audio_files(dir_path)
    if #dir_files > 0 then
      local dir_config = parse_sample_config(dir_path)
      table.insert(groups, {name = dir_name, files = dir_files, config = dir_config})
    end
  end

  -- Flood-fill layout into grid rows 3-16, cols 1-16 (224 slots)
  local MIN_ROW, MAX_ROW = 3, 8
  local MIN_COL, MAX_COL = 1, 16

  local occupied = {}
  for r = MIN_ROW, MAX_ROW do
    occupied[r] = {}
    for c = MIN_COL, MAX_COL do
      local has_snap = S.grid_snapshots[r] and S.grid_snapshots[r][c]
      occupied[r][c] = S.is_prime_slot(r, c) or (has_snap ~= nil)
    end
  end

  local function find_first_empty()
    for r = MIN_ROW, MAX_ROW do
      for c = MIN_COL, MAX_COL do
        if not occupied[r][c] then return r, c end
      end
    end
    return nil, nil
  end

  local function flood_fill(seed_row, seed_col, count)
    local cells = {}
    local frontier = {{seed_row, seed_col}}
    local in_frontier = {}
    in_frontier[seed_row * 100 + seed_col] = true

    while #cells < count and #frontier > 0 do
      local cell = table.remove(frontier, 1)
      local r, c = cell[1], cell[2]
      in_frontier[r * 100 + c] = nil

      if not occupied[r][c] then
        table.insert(cells, {r, c})
        occupied[r][c] = true

        local neighbors = {{r-1, c}, {r+1, c}, {r, c-1}, {r, c+1}}
        for _, nb in ipairs(neighbors) do
          local nr, nc = nb[1], nb[2]
          if nr >= MIN_ROW and nr <= MAX_ROW and nc >= MIN_COL and nc <= MAX_COL
            and not occupied[nr][nc] and not in_frontier[nr * 100 + nc] then
            local dist = math.max(math.abs(nr - seed_row), math.abs(nc - seed_col))
            local key_new = dist * 10000 + nr * 100 + nc
            local inserted = false
            for i = 1, #frontier do
              local fi = frontier[i]
              local dist_i = math.max(math.abs(fi[1] - seed_row), math.abs(fi[2] - seed_col))
              local key_i = dist_i * 10000 + fi[1] * 100 + fi[2]
              if key_new < key_i then
                table.insert(frontier, i, {nr, nc})
                inserted = true
                break
              end
            end
            if not inserted then
              table.insert(frontier, {nr, nc})
            end
            in_frontier[nr * 100 + nc] = true
          end
        end
      end
    end

    table.sort(cells, function(a, b)
      if a[1] ~= b[1] then return a[1] < b[1] end
      return a[2] < b[2]
    end)

    return cells
  end

  for g_idx = 1, #groups do
    local group = groups[g_idx]
    local file_count = math.min(#group.files, MAX_SAMPLES - S.num_samples)
    if file_count <= 0 then break end

    local seed_r, seed_c = find_first_empty()
    if not seed_r then break end

    local cells = flood_fill(seed_r, seed_c, file_count)

    for fi = 1, #cells do
      if fi > #group.files or S.num_samples >= MAX_SAMPLES then break end
      local r, c = cells[fi][1], cells[fi][2]
      local filepath = group.files[fi]
      local name = display_name(filepath)
      local cfg = group.config and group.config[name] or {}
      S.num_samples = S.num_samples + 1
      S.samples[S.num_samples] = {
        filepath = filepath,
        name = name,
        slot = S.num_samples - 1,
        grid_row = r,
        grid_col = c,
        group_idx = g_idx,
        rate = cfg.rate or 1.0,
      }
      S.pad_amps[S.num_samples] = cfg.amp or 1.0
      if not S.grid_samples[r] then S.grid_samples[r] = {} end
      S.grid_samples[r][c] = S.num_samples
    end

    S.group_names[g_idx] = group.name

    print("erasmus: group " .. g_idx .. " [" .. group.name .. "] " ..
      #cells .. " samples (flood-fill from row " .. seed_r .. ", col " .. seed_c .. ")")
  end

  compute_group_brightness(#groups)

  print("erasmus: " .. S.num_samples .. " total samples in " ..
    #groups .. " groups")
end

-- Add per-sample amp params to the norns params system.
function Samples.add_params()
  if S.num_samples == 0 then return end
  params:add_group("sample_levels", "Sample Levels", S.num_samples)
  for i = 1, S.num_samples do
    params:add_control(
      "sample_" .. i .. "_amp",
      S.samples[i].name,
      controlspec.new(0.25, 4.0, 'lin', 0.01, 1.0, "x")
    )
    params:set_action("sample_" .. i .. "_amp", function(value)
      S.pad_amps[i] = value
      S.is_screen_dirty = true
    end)
  end
end

-- Load all sample WAVs into the MxSamples engine (runs in a clock coroutine).
function Samples.load_into_engine()
  for i = 1, S.num_samples do
    engine.mxsamplesload(S.samples[i].slot, S.samples[i].filepath)
    print("  loading [" .. i .. "/" .. S.num_samples .. "] " .. S.samples[i].name)
  end
  Snapshots.load_into_engine()
  print("erasmus: all samples loaded")
  S.grid_dirty = true
  S.is_screen_dirty = true
end

-- Trigger a sample through the engine.
function Samples.trigger(idx)
  if idx < 1 or idx > S.num_samples then return end
  local s = S.samples[idx]

  local amp = S.pad_amps[idx] or 1.0
  local rate = s.rate or 1.0
  engine.mxsampleson(idx, s.slot, rate, amp, 0.0, 0.015, 1.0, 0.9, 0.5, 20000, 10, 0.0, 0.0, 0)
  S.current_playing_pad = idx

  local ti = S.recording_target
  S.track_writing_name[ti] = s.name

  S.track_trigger_this_loop[ti] = true
  if not S.track_preserve_boosted[ti] and not S.track_preserve0_held[ti] then
    S.track_preserve_boosted[ti] = true
    S.tracks[ti]:set_pre_level(1.0)
  end

  S.grid_dirty = true
  S.is_screen_dirty = true
end

-- Stop engine playback of a sample.
function Samples.stop(idx)
  if idx < 1 or idx > S.num_samples then return end
  engine.mxsamplesoff(idx)
  if S.current_playing_pad == idx then
    S.current_playing_pad = nil
  end
end

return Samples
