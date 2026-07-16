#pragma once

#include <cstdint>
#include "driver/ledc.h"
#include "esp_err.h"
#include "bsp.hh"

// Buzzer driver: a square-wave siren on a single GPIO via LEDC PWM.
//
// The tone is a 50%-duty square wave whose frequency is swept up and down to produce a classic
// wailing-siren sound. SetSiren(true/false) requests the siren on or off; Update() (called each main-
// loop iteration) advances the frequency sweep non-blockingly, so nothing here blocks the loop.
//
// Uses its own LEDC timer + channel (from bsp), distinct from the EPD front light's LEDC resources.
class Buzzer {
 public:
  struct Config {
    gpio_num_t     pin        = bsp.buzzer_pin;
    ledc_timer_t   ledc_timer   = bsp.buzzer_ledc_timer;
    ledc_channel_t ledc_channel = bsp.buzzer_ledc_channel;
    ledc_mode_t    speed_mode   = LEDC_LOW_SPEED_MODE;
    // 8-bit duty resolution is plenty for a 50% square wave and keeps the max usable frequency high.
    ledc_timer_bit_t duty_resolution = LEDC_TIMER_8_BIT;

    // Siren sweep parameters.
    uint32_t freq_min_hz     = 2400;    // sweep low end
    uint32_t freq_max_hz     = 3000;   // sweep high end
    uint32_t sweep_period_ms = 1000;   // full up+down cycle (500 ms each way)
  };

  Buzzer() : Buzzer(Config{}) {}
  explicit Buzzer(const Config& config);
  ~Buzzer();

  Buzzer(const Buzzer&)            = delete;
  Buzzer& operator=(const Buzzer&) = delete;

  // Configures the LEDC timer/channel for this buzzer (silent). Returns false on failure.
  bool Init();

  // Silences the buzzer and releases the LEDC channel. Idempotent.
  bool Deinit();

  bool IsInitialized() const { return ready_; }

  // Requests the siren on or off. Cheap; the actual tone is driven by Update().
  void SetSiren(bool on) { siren_on_ = on; }

  // Advances the frequency sweep while the siren is on (self-timed). Call once per main-loop
  // iteration. Returns false on an LEDC error.
  bool Update();

 private:
  // Sets the square-wave output on (50% duty at freq_hz) or off (0% duty).
  bool SetToneHz(uint32_t freq_hz);
  bool SetSilent();

  const Config config_;

  bool     ready_    = false;
  bool     siren_on_ = false;
  bool     tone_active_ = false;   // true while the channel is driving a tone (avoid redundant writes)

  // Self-timed sweep phase in [0, 1): 0->0.5 ramps freq up, 0.5->1 ramps down.
  float   sweep_phase_    = 0.0f;
  int64_t last_update_us_ = 0;     // 0 = first call
  uint32_t max_duty_      = 0;     // (1 << duty_resolution) - 1, computed at Init()
};
