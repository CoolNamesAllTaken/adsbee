#include "buzzer.hh"

#include "esp_log.h"
#include "esp_timer.h"

static const char* kTag = "Buzzer";

Buzzer::Buzzer(const Config& config) : config_(config) {}

Buzzer::~Buzzer() {
  if (ready_) {
    Deinit();
  }
}

bool Buzzer::Init() {
  if (ready_) {
    ESP_LOGW(kTag, "Already initialized.");
    return false;
  }

  max_duty_ = (1u << config_.duty_resolution) - 1u;

  // Configure the LEDC timer at the low end of the sweep (frequency is changed at runtime).
  ledc_timer_config_t timer_cfg = {};
  timer_cfg.speed_mode      = config_.speed_mode;
  timer_cfg.duty_resolution = config_.duty_resolution;
  timer_cfg.timer_num       = config_.ledc_timer;
  timer_cfg.freq_hz         = config_.freq_min_hz;
  timer_cfg.clk_cfg         = LEDC_AUTO_CLK;
  esp_err_t ret = ledc_timer_config(&timer_cfg);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "LEDC timer config failed: %s", esp_err_to_name(ret));
    return false;
  }

  ledc_channel_config_t ch_cfg = {};
  ch_cfg.gpio_num   = config_.pin;
  ch_cfg.speed_mode = config_.speed_mode;
  ch_cfg.channel    = config_.ledc_channel;
  ch_cfg.timer_sel  = config_.ledc_timer;
  ch_cfg.duty       = 0;  // Start silent.
  ch_cfg.hpoint     = 0;
  ret = ledc_channel_config(&ch_cfg);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "LEDC channel config failed: %s", esp_err_to_name(ret));
    return false;
  }

  ready_ = true;
  ESP_LOGI(kTag, "Initialized (GPIO%d, timer %d, channel %d).", config_.pin, config_.ledc_timer,
           config_.ledc_channel);
  return true;
}

bool Buzzer::Deinit() {
  if (!ready_) {
    return true;
  }
  ledc_stop(config_.speed_mode, config_.ledc_channel, 0);
  ready_       = false;
  siren_on_    = false;
  tone_active_ = false;
  ESP_LOGI(kTag, "Deinitialized.");
  return true;
}

bool Buzzer::SetToneHz(uint32_t freq_hz) {
  if (ledc_set_freq(config_.speed_mode, config_.ledc_timer, freq_hz) != ESP_OK) {
    return false;
  }
  // 50% duty square wave.
  if (ledc_set_duty(config_.speed_mode, config_.ledc_channel, max_duty_ / 2u) != ESP_OK ||
      ledc_update_duty(config_.speed_mode, config_.ledc_channel) != ESP_OK) {
    return false;
  }
  tone_active_ = true;
  return true;
}

bool Buzzer::SetSilent() {
  if (ledc_set_duty(config_.speed_mode, config_.ledc_channel, 0) != ESP_OK ||
      ledc_update_duty(config_.speed_mode, config_.ledc_channel) != ESP_OK) {
    return false;
  }
  tone_active_ = false;
  return true;
}

bool Buzzer::Update() {
  if (!ready_) {
    return false;
  }

  if (!siren_on_) {
    // Silence once when transitioning to off; reset the sweep so it starts low next time.
    if (tone_active_) {
      sweep_phase_    = 0.0f;
      last_update_us_ = 0;
      return SetSilent();
    }
    return true;
  }

  // Self-timed sweep advance.
  const int64_t now_us = esp_timer_get_time();
  float dt = 0.0f;
  if (last_update_us_ != 0) {
    dt = (now_us - last_update_us_) * 1e-6f;
  }
  last_update_us_ = now_us;

  const float period_s = config_.sweep_period_ms / 1000.0f;
  if (period_s > 0.0f) {
    sweep_phase_ += dt / period_s;
    while (sweep_phase_ >= 1.0f) sweep_phase_ -= 1.0f;
  }

  // Triangle wave over the sweep: 0..0.5 ramps up, 0.5..1 ramps down.
  float tri = (sweep_phase_ < 0.5f) ? (sweep_phase_ * 2.0f) : (2.0f - sweep_phase_ * 2.0f);
  uint32_t freq_hz =
      config_.freq_min_hz + static_cast<uint32_t>(tri * (config_.freq_max_hz - config_.freq_min_hz));

  return SetToneHz(freq_hz);
}
