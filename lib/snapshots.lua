-- lib/snapshots.lua
-- Scene snapshot management: save, load, scan, engine playback.
-- Each snapshot stores all 3 track buffers + BPM + beat counts as stereo WAV files.

local Snapshots = {}

local SNAPSHOT_DIR = _path.audio .. "erasmus/snapshots/"
local snapshot_dir_ready = false

-- Module-level reference to shared state (set by init)
local S

function Snapshots.init(state)
  S = state
end

local function ensure_snapshot_dir()
  if not snapshot_dir_ready then
    os.execute("mkdir -p '" .. SNAPSHOT_DIR .. "'")
    snapshot_dir_ready = true
  end
end

-- Load a snapshot's WAV files into engine slots for sample-style playback
local function load_snapshot_into_engine(snap)
  snap.engine_slots = {}
  for ti = 1, 3 do
    local path = SNAPSHOT_DIR .. snap.base .. "_t" .. ti .. ".wav"
    local f = io.open(path, "r")
    if f then
      f:close()
      local slot = S.next_engine_slot
      S.next_engine_slot = S.next_engine_slot + 1
      snap.engine_slots[ti] = slot
      engine.mxsamplesload(slot, path)
    end
  end
end

-- Scan snapshot directory and populate state.snapshots + state.grid_snapshots.
-- Called during init before sample scanning.
function Snapshots.scan()
  ensure_snapshot_dir()
  S.snapshots = {}
  S.grid_snapshots = {}

  local entries = util.scandir(SNAPSHOT_DIR)
  if not entries then return end

  local seen = {}
  for _, entry in ipairs(entries) do
    local base = entry:match("^(snap_r%d+c%d+_bpm[%d%.]+_b%d+_%d+_%d+)_t%d%.wav$")
    if base and not seen[base] then
      seen[base] = true
      local row, col, bpm, b1, b2, b3 = base:match(
        "^snap_r(%d+)c(%d+)_bpm([%d%.]+)_b(%d+)_(%d+)_(%d+)$")
      row = tonumber(row)
      col = tonumber(col)
      bpm = tonumber(bpm)
      b1 = tonumber(b1)
      b2 = tonumber(b2)
      b3 = tonumber(b3)
      if row and col and bpm and b1 and b2 and b3 then
        local snap = {grid_row = row, grid_col = col, base = base, bpm = bpm, beats = {b1, b2, b3}}
        table.insert(S.snapshots, snap)
        if not S.grid_snapshots[row] then S.grid_snapshots[row] = {} end
        S.grid_snapshots[row][col] = #S.snapshots
        print("erasmus: found snapshot " .. base)
      end
    end
  end
end

-- Load all snapshot WAVs into engine slots (called after samples are loaded).
function Snapshots.load_into_engine()
  S.next_engine_slot = S.num_samples
  for _, snap in ipairs(S.snapshots) do
    load_snapshot_into_engine(snap)
  end
end

-- Save current state of all 3 tracks as a snapshot.
function Snapshots.save()
  ensure_snapshot_dir()
  local row, col = S.find_free_snapshot_slot()
  if not row then
    print("erasmus: no free grid slot for snapshot")
    return
  end

  local bpm = params:get("clock_tempo")
  local b1 = S.tracks[1].num_beats
  local b2 = S.tracks[2].num_beats
  local b3 = S.tracks[3].num_beats
  local base = string.format("snap_r%dc%d_bpm%g_b%d_%d_%d", row, col, bpm, b1, b2, b3)

  for ti = 1, 3 do
    local t = S.tracks[ti]
    local off = t.buffer_offset
    local dur = t.buffer_dur
    if dur > 0 then
      softcut.buffer_write_stereo(SNAPSHOT_DIR .. base .. "_t" .. ti .. ".wav", off, dur)
    end
  end

  local snap = {grid_row = row, grid_col = col, base = base, bpm = bpm, beats = {b1, b2, b3}}
  table.insert(S.snapshots, snap)
  if not S.grid_snapshots[row] then S.grid_snapshots[row] = {} end
  S.grid_snapshots[row][col] = #S.snapshots

  load_snapshot_into_engine(snap)

  S.snapshot_flash_time = util.time()
  S.grid_dirty = true
  S.is_screen_dirty = true
  print("erasmus: saved snapshot to " .. base)
end

-- Apply snapshot state to all 3 tracks (effects, timing, iso).
-- Does NOT touch the buffer content — caller decides whether to read WAVs.
local function apply_snapshot_state(snap)
  -- Clear all effect state — these were baked into the snapshot audio.
  for ti = 1, 3 do
    S.tracks[ti].pitch_shift_semitones = 0
    S.tracks[ti].reversed = false
    S.track_reversed[ti] = false
    S.track_iso_kills[ti] = {false, false, false}
    S.track_writing_name[ti] = nil
  end

  -- load_state sets buffer_dur, loop_dur, rate=1.0, resets position,
  -- clears iso data and name data lanes.
  -- Then fill name_data with the snapshot name so the screen shows it
  -- as a backdrop that gets overwritten as new material is added.
  local snap_name = string.format("s%d.%d", snap.grid_row, snap.grid_col)
  for ti = 1, 3 do
    S.tracks[ti]:load_state(snap.bpm, snap.beats[ti])
    S.tracks[ti]:update_iso(false, false, false)
    S.tracks[ti]:fill_name_data(snap_name)
  end

  params:set("clock_tempo", snap.bpm)
  S.refresh_input_routing()
  S.snapshot_flash_time = util.time()
  S.grid_dirty = true
  S.is_screen_dirty = true
end

-- Load a snapshot into all 3 track buffers (from WAV files on disk).
-- Clears all baked-in effects (pitch, reverse, iso, data lanes).
function Snapshots.load(row, col)
  if not S.grid_snapshots[row] or not S.grid_snapshots[row][col] then return end
  local snap_idx = S.grid_snapshots[row][col]
  local snap = S.snapshots[snap_idx]
  if not snap then return end

  apply_snapshot_state(snap)

  -- Read WAV files into buffers
  for ti = 1, 3 do
    local t = S.tracks[ti]
    local path = SNAPSHOT_DIR .. snap.base .. "_t" .. ti .. ".wav"
    if t.buffer_dur > 0 then
      softcut.buffer_read_stereo(path, 0, t.buffer_offset, t.buffer_dur)
    end
  end

  print("erasmus: loaded snapshot " .. snap.base)
end

-- Apply snapshot state WITHOUT reading WAV files into buffers.
-- Used after recording: the buffer already has the right content, and the
-- WAV files may not be written yet (buffer_write_stereo is async).
function Snapshots.apply_state(row, col)
  if not S.grid_snapshots[row] or not S.grid_snapshots[row][col] then return end
  local snap_idx = S.grid_snapshots[row][col]
  local snap = S.snapshots[snap_idx]
  if not snap then return end

  apply_snapshot_state(snap)
  print("erasmus: applied snapshot state " .. snap.base)
end

-- Play a snapshot through the engine like a sample (when buffer rec is off).
function Snapshots.trigger_as_sample(snap_idx)
  local snap = S.snapshots[snap_idx]
  if not snap or not snap.engine_slots then return end

  for ti = 1, 3 do
    local slot = snap.engine_slots[ti]
    if slot then
      local amp = 1.0
      engine.mxsampleson(slot + 1, slot, 1.0, amp, 0.0, 0.015, 1.0, 0.9, 0.5, 20000, 10, 0.0, 0.0, 0)
    end
  end
  S.current_playing_snapshot = snap_idx

  local ti = S.recording_target
  S.track_trigger_this_loop[ti] = true
  if not S.track_preserve_boosted[ti] and not S.track_preserve0_held[ti] then
    S.track_preserve_boosted[ti] = true
    S.tracks[ti]:set_pre_level(1.0)
  end

  S.grid_dirty = true
  S.is_screen_dirty = true
end

-- Stop engine playback of a snapshot.
function Snapshots.stop_playback()
  if not S.current_playing_snapshot then return end
  local snap = S.snapshots[S.current_playing_snapshot]
  if snap and snap.engine_slots then
    for ti = 1, 3 do
      local slot = snap.engine_slots[ti]
      if slot then
        engine.mxsamplesoff(slot + 1)
      end
    end
  end
  S.current_playing_snapshot = nil
end

return Snapshots
