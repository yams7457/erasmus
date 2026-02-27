-- lib/looper.lua
-- Samsara-style softcut looper module
-- Adapted from samsara v1.4.3 by @21echoes
-- Two softcut voices (1=L, 2=R) forming a stereo delay loop
-- Post-filter used for DJ-style isolator kills (output only, doesn't affect recording)
--
-- Uses softcut native looping for sample-accurate timing.
-- The clock coroutine only drives the UI beat counter.
--
-- Delay-line model: loop_start is fixed at 0, loop_end = delay time.
-- Changing beats/tempo just moves loop_end. pre_level is feedback,
-- rec_level is input mix. On resize, buffer content is rearranged
-- to preserve the most recently heard output. Softcut handles the rest.

local Looper = {}
Looper.__index = Looper

local MAX_NUM_BEATS = 32

function Looper.new()
  local self = setmetatable({}, Looper)
  self.playing = 1
  self.rec_level = 1.0
  self.pre_level = 1.0
  self.num_beats = 8
  self.tempo = 120
  self.loop_dur = (8 / 120) * 60 -- default
  self.loop_start_pos = 0        -- buffer position of loop start (always 0)
  self.loop_end_pos = 0          -- buffer position of loop end (set in init)
  self.playhead_pos = 0          -- tracked via phase polling
  self.cur_beat = 0
  self.clock_id = nil
  self.on_beat_callback = nil
  self.buffer_muted = false

  -- Audio level state for restore
  self.initial_levels = {}
  self.modified_level_params = {
    "cut_input_adc",
    "cut_input_eng",
    "cut_input_tape",
    "monitor_level",
    "softcut_level",
  }
  return self
end

function Looper:init()
  -- Save initial audio levels and configure routing
  for _, level_param in ipairs(self.modified_level_params) do
    self.initial_levels[level_param] = params:get(level_param)
  end

  -- Engine -> softcut ON (this is our sample source)
  params:set("cut_input_eng", 0)
  -- ADC -> softcut OFF (controlled by momentary button)
  params:set("cut_input_adc", -math.huge)
  -- Tape -> softcut OFF
  params:set("cut_input_tape", -math.huge)
  -- ADC -> DAC OFF (controlled by momentary button)
  params:set("monitor_level", -math.huge)
  -- Softcut -> DAC ON
  params:set("softcut_level", 0)

  softcut.buffer_clear()

  self.loop_start_pos = 0

  for voice = 1, 2 do
    softcut.enable(voice, 1)
    softcut.buffer(voice, voice)
    softcut.pan(voice, voice == 1 and -1.0 or 1.0)
    softcut.rate(voice, 1)
    -- Native looping for sample-accurate wrap
    softcut.loop(voice, 1)
    softcut.loop_start(voice, 0)
    softcut.position(voice, 0)
    -- Route engine stereo into softcut: L->voice1, R->voice2
    softcut.level_input_cut(1, voice, voice == 1 and 1.0 or 0.0)
    softcut.level_input_cut(2, voice, voice == 2 and 1.0 or 0.0)
    -- Output level always 1.0 (preserve only affects buffer feedback)
    softcut.level(voice, 1.0)
    softcut.pre_level(voice, self.pre_level)
    softcut.rec_level(voice, self.rec_level)
    -- Short slew on rec/pre to avoid clicks but stay punchy
    softcut.level_slew_time(voice, 0.01)
    softcut.recpre_slew_time(voice, 0.01)
    softcut.rec(voice, 1)
    softcut.play(voice, 1)
  end

  -- Post-filter: passthrough by default (dry=1, all taps=0)
  for voice = 1, 2 do
    softcut.post_filter_dry(voice, 1.0)
    softcut.post_filter_lp(voice, 0)
    softcut.post_filter_hp(voice, 0)
    softcut.post_filter_bp(voice, 0)
    softcut.post_filter_br(voice, 0)
  end

  -- Phase polling to track playhead for content-preserving resize
  local this = self
  softcut.event_phase(function(voice, pos)
    if voice == 1 then
      this.playhead_pos = pos
    end
  end)
  softcut.phase_quant(1, 1/30)

  -- Set initial loop_end
  self.loop_dur = (self.num_beats / self.tempo) * 60
  self:_apply_loop_end()
end

function Looper:start_clock()
  self.cur_beat = 0
  self.clock_id = clock.run(function()
    while true do
      clock.sync(1)
      if self.playing == 1 then
        -- UI beat counter only -- softcut handles its own looping
        self.cur_beat = (self.cur_beat + 1) % self.num_beats

        if self.on_beat_callback then
          self.on_beat_callback(self.cur_beat)
        end
      end
    end
  end)
end

function Looper:set_pre_level(val)
  self.pre_level = val
  for voice = 1, 2 do
    softcut.pre_level(voice, val)
  end
end

function Looper:set_rec_level(val)
  self.rec_level = val
  if not self.buffer_muted then
    for voice = 1, 2 do
      softcut.rec_level(voice, val)
    end
  end
end

function Looper:set_num_beats(val)
  self.num_beats = util.clamp(val, 1, MAX_NUM_BEATS)
  self.loop_dur = (self.num_beats / self.tempo) * 60
  self:_resize_loop()
end

function Looper:set_tempo(bpm)
  self.tempo = bpm
  self.loop_dur = (self.num_beats / self.tempo) * 60
  self:_resize_loop()
end

function Looper:set_playing(val)
  if val == 1 then
    -- Resume
    for voice = 1, 2 do
      softcut.enable(voice, 1)
      if not self.buffer_muted then
        softcut.rec_level(voice, self.rec_level)
        softcut.level(voice, 1.0)
      else
        softcut.rec_level(voice, 0)
        softcut.level(voice, 0)
      end
    end
    self.playing = 1
  else
    -- Pause
    for voice = 1, 2 do
      softcut.rec_level(voice, 0.0)
      softcut.level(voice, 0.0)
      softcut.enable(voice, 0)
    end
    self.playing = 0
  end
end

function Looper:set_buffer_muted(muted)
  self.buffer_muted = muted
  for voice = 1, 2 do
    if muted then
      softcut.rec_level(voice, 0)
      softcut.level(voice, 0)
    else
      softcut.rec_level(voice, self.rec_level)
      softcut.level(voice, 1.0)
    end
  end
end

function Looper:get_cur_beat()
  return self.cur_beat
end

function Looper:get_loop_dur()
  return self.loop_dur
end

function Looper:get_num_beats()
  return self.num_beats
end

function Looper:get_playing()
  return self.playing
end

function Looper:cleanup()
  -- Cancel clock
  if self.clock_id then
    clock.cancel(self.clock_id)
    self.clock_id = nil
  end

  -- Restore prior audio levels
  for level_param, level in pairs(self.initial_levels) do
    params:set(level_param, level)
  end
end

-- Content-preserving loop resize.
-- On shrink: copies the most recently heard content to [0, new_dur].
-- On expand: tiles existing content to fill [old_dur, new_dur].
function Looper:_resize_loop()
  local old_end = self.loop_end_pos
  local new_end = self.loop_dur

  if new_end < old_end and old_end > 0 then
    -- Shrinking: preserve the last new_end seconds of output.
    -- That content lives at [P - new_end, P] in the old buffer (wrapping).
    local p = self.playhead_pos
    local src = p - new_end
    if src >= 0 then
      -- No wrap: forward copy is safe (dst=0 < src)
      for ch = 1, 2 do
        softcut.buffer_copy_mono(ch, ch, src, 0, new_end, 0, 0)
      end
    else
      -- Wrap: assemble in staging area (pos 300) to avoid overlap
      local staging = 300
      local wrap_src = old_end + src
      local first_len = old_end - wrap_src
      local second_len = new_end - first_len
      for ch = 1, 2 do
        softcut.buffer_copy_mono(ch, ch, wrap_src, staging, first_len, 0, 0)
        if second_len > 0 then
          softcut.buffer_copy_mono(ch, ch, 0, staging + first_len, second_len, 0, 0)
        end
        softcut.buffer_copy_mono(ch, ch, staging, 0, new_end, 0, 0)
      end
    end
    -- Don't reposition playhead — softcut wraps it naturally when
    -- loop_end moves inward, preserving timing continuity.
  elseif new_end > old_end and old_end > 0 then
    -- Expanding: tile existing content into the new region
    local pos = old_end
    while pos < new_end do
      local chunk = math.min(old_end, new_end - pos)
      for ch = 1, 2 do
        softcut.buffer_copy_mono(ch, ch, 0, pos, chunk, 0, 0)
      end
      pos = pos + chunk
    end
  end

  self:_apply_loop_end()
end

-- Internal: set softcut loop_end from current state.
-- loop_start is always 0, so loop_end = loop_dur.
function Looper:_apply_loop_end()
  self.loop_end_pos = self.loop_dur
  for voice = 1, 2 do
    softcut.loop_end(voice, self.loop_end_pos)
  end
end

function Looper:set_iso_cut(band)
  for voice = 1, 2 do
    softcut.post_filter_dry(voice, 0)
    if band == "low" then
      softcut.post_filter_hp(voice, 1.0)
      softcut.post_filter_lp(voice, 0)
      softcut.post_filter_bp(voice, 0)
      softcut.post_filter_br(voice, 0)
      softcut.post_filter_fc(voice, 250)
      softcut.post_filter_rq(voice, 2.0)
    elseif band == "mid" then
      softcut.post_filter_br(voice, 1.0)
      softcut.post_filter_lp(voice, 0)
      softcut.post_filter_hp(voice, 0)
      softcut.post_filter_bp(voice, 0)
      softcut.post_filter_fc(voice, 935)
      softcut.post_filter_rq(voice, 3.5)
    elseif band == "high" then
      softcut.post_filter_lp(voice, 1.0)
      softcut.post_filter_hp(voice, 0)
      softcut.post_filter_bp(voice, 0)
      softcut.post_filter_br(voice, 0)
      softcut.post_filter_fc(voice, 3500)
      softcut.post_filter_rq(voice, 2.0)
    end
  end
end

function Looper:clear_iso_cut()
  for voice = 1, 2 do
    softcut.post_filter_dry(voice, 1.0)
    softcut.post_filter_lp(voice, 0)
    softcut.post_filter_hp(voice, 0)
    softcut.post_filter_bp(voice, 0)
    softcut.post_filter_br(voice, 0)
  end
end

function Looper:beat_shuffle(group_size)
  local n = math.floor(self.num_beats / group_size)
  if n < 2 then return end
  local group_dur = group_size * self.loop_dur / self.num_beats
  local staging = self.loop_end_pos
  -- Double-copy staging so wrapped reads are contiguous
  if staging + 2 * self.loop_dur > 350 then return end
  local fade = group_dur > 0.01 and 0.002 or 0
  local offset = self.playhead_pos % self.loop_dur

  local order = {}
  for i = 1, n do order[i] = i end
  for i = n, 2, -1 do
    local j = math.random(i)
    order[i], order[j] = order[j], order[i]
  end

  for ch = 1, 2 do
    -- Two copies in staging so any offset+group read stays in bounds
    softcut.buffer_copy_mono(ch, ch, 0, staging, self.loop_dur, 0, 0)
    softcut.buffer_copy_mono(ch, ch, 0, staging + self.loop_dur, self.loop_dur, 0, 0)

    for dst = 1, n do
      local src_start = offset + (order[dst] - 1) * group_dur
      local dst_start = (offset + (dst - 1) * group_dur) % self.loop_dur

      if dst_start + group_dur <= self.loop_dur then
        softcut.buffer_copy_mono(ch, ch,
          staging + src_start, dst_start, group_dur, fade, 0)
      else
        -- Group wraps around loop boundary: split into two copies
        local first = self.loop_dur - dst_start
        softcut.buffer_copy_mono(ch, ch,
          staging + src_start, dst_start, first, fade, 0)
        softcut.buffer_copy_mono(ch, ch,
          staging + src_start + first, 0, group_dur - first, fade, 0)
      end
    end
  end
end

return Looper
