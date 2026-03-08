-- lib/recording.lua
-- Record arm state machine and BPM detection.
-- Uses norns tape recorder to capture the full DAC output (engine + softcut
-- playback = exactly what the performer hears). This is faithful even when
-- cue points jump the playhead, because the tape records the mix output.
-- Flow: idle -> armed -> (sample/cue press) -> recording -> (col 15 press) -> idle

local Recording = {}

-- Module-level references (set by init)
local S
local Snapshots

function Recording.init(state, snapshots)
  S = state
  Snapshots = snapshots
end

-- Detect BPM and beat count from a recording duration.
-- Prefers power-of-2 beat counts, falls back to closest to 90 BPM.
local function calculate_bpm(duration)
  local valid = {}
  for b = 1, 32 do
    local bpm = 60 * b / duration
    if bpm >= 60 and bpm <= 119 then
      table.insert(valid, b)
    end
  end

  if #valid == 0 then
    return 60 / duration, 1
  end

  local best_pow2 = nil
  for _, b in ipairs(valid) do
    if b > 0 and (b & (b - 1)) == 0 then
      if not best_pow2 or b > best_pow2 then
        best_pow2 = b
      end
    end
  end
  if best_pow2 then
    return 60 * best_pow2 / duration, best_pow2
  end

  local best_b = valid[1]
  local best_dist = math.abs(60 * valid[1] / duration - 90)
  for i = 2, #valid do
    local dist = math.abs(60 * valid[i] / duration - 90)
    if dist < best_dist then
      best_dist = dist
      best_b = valid[i]
    end
  end
  return 60 * best_b / duration, best_b
end

local CAPTURE_PATH = _path.audio .. "erasmus/capture_tmp.wav"

-- Begin recording if armed (called from grid handler on sample/cue press).
function Recording.begin_if_armed()
  if S.rec_state ~= "armed" or S.tracks[S.recording_target].capturing then return end
  S.tracks[S.recording_target]:start_recording()
  S.rec_state = "recording"
end

-- Stop recording: tape capture → read into buffer → detect BPM → save snapshot.
local function stop_recording()
  local ti = S.recording_target
  local t = S.tracks[ti]

  local wallclock = t:stop_recording()
  local duration = util.clamp(wallclock, 0.5, t.region_size)

  -- Read the tape capture into the recording target's buffer region
  softcut.buffer_clear_region(t.buffer_offset, t.region_size)
  softcut.buffer_read_stereo(CAPTURE_PATH, 0, t.buffer_offset, duration)

  -- Detect BPM and beats (prefers power-of-2 beat count, 60-119 BPM range)
  local bpm, beats = calculate_bpm(duration)

  -- Set track state so the snapshot saves correct metadata
  t.buffer_dur = duration
  t.num_beats = beats
  t.tempo = bpm
  t.loop_dur = duration
  t.rate = 1.0
  t:_apply_loop_end()

  S.rec_state = "idle"

  -- Set tempo before saving so the snapshot encodes the correct BPM
  params:set("clock_tempo", bpm)

  -- Save as snapshot, then apply state (timing, effects reset) to all 3 tracks.
  -- Don't re-read WAVs — the buffer already has the recording.
  Snapshots.save()
  local snap = S.snapshots[#S.snapshots]
  if snap then
    Snapshots.apply_state(snap.grid_row, snap.grid_col)
  end

  print("erasmus: recording complete — " .. string.format("%.1fs", duration) ..
    " @ " .. string.format("%.1f", bpm) .. " BPM, " .. beats .. " beats")
end

-- Toggle rec arm state machine (called from grid col 15).
function Recording.toggle()
  if S.rec_state == "idle" then
    S.rec_state = "armed"
  elseif S.rec_state == "armed" then
    S.rec_state = "idle"
  elseif S.rec_state == "recording" then
    stop_recording()
  end
  S.grid_dirty = true
  S.is_screen_dirty = true
end

return Recording
