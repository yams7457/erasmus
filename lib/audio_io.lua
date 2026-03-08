-- lib/audio_io.lua
-- Audio input/output routing for external audio (ADC).
--
-- Controls:
--   audio.level_adc_cut(level) — ADC → softcut input bus (for recording into buffer)
--   audio.level_adc(level)     — ADC → DAC (input monitoring)
-- Both are standard script-level controls. norns restores system defaults
-- on script exit, so we won't permanently alter the user's LEVELS settings.

local AudioIO = {}

-- Module-level reference to shared state (set by init)
local S

function AudioIO.init(state)
  S = state

  -- Start with ADC routing off
  S.adc_to_softcut = 0
  S.adc_monitor = 0

  -- Zero both paths so external audio doesn't leak on startup
  audio.level_adc_cut(0)
  audio.level_adc(0)
end

-- Enable/disable ADC → softcut (for recording external audio into the buffer).
function AudioIO.set_adc_to_softcut(level)
  S.adc_to_softcut = level
  audio.level_adc_cut(level)
end

-- Enable/disable ADC → DAC (hear the input directly).
function AudioIO.set_monitor(level)
  S.adc_monitor = level
  audio.level_adc(level)
end

return AudioIO
