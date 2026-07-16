#include "co_sensor.hh"

#include "esp_adc/adc_cali_scheme.h"
#include "esp_log.h"

static const char* kTag = "CO";

CoSensor::CoSensor(const Config& config) : config_(config) {}

CoSensor::~CoSensor() {
  if (adc_handle_ != nullptr) {
    Deinit();
  }
}

bool CoSensor::Init() {
  if (adc_handle_ != nullptr) {
    ESP_LOGW(kTag, "Already initialized.");
    return false;
  }

  // Resolve ADC unit + channel from the configured GPIOs.
  adc_unit_t    vout_unit, vref_unit;
  esp_err_t     ret = adc_oneshot_io_to_channel(config_.vout_pin, &vout_unit, &vout_channel_);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "CO_VOUT GPIO%d is not ADC-capable: %s", config_.vout_pin, esp_err_to_name(ret));
    return false;
  }
  ret = adc_oneshot_io_to_channel(config_.vref_pin, &vref_unit, &vref_channel_);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "CO_VREF GPIO%d is not ADC-capable: %s", config_.vref_pin, esp_err_to_name(ret));
    return false;
  }
  if (vout_unit != vref_unit) {
    ESP_LOGE(kTag, "CO_VOUT (unit %d) and CO_VREF (unit %d) must be on the same ADC unit.", vout_unit,
             vref_unit);
    return false;
  }
  adc_unit_ = vout_unit;

  // Bring up the ADC oneshot unit.
  adc_oneshot_unit_init_cfg_t unit_cfg = {};
  unit_cfg.unit_id = adc_unit_;
  ret = adc_oneshot_new_unit(&unit_cfg, &adc_handle_);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "adc_oneshot_new_unit failed: %s", esp_err_to_name(ret));
    adc_handle_ = nullptr;
    return false;
  }

  // Configure both channels with the same attenuation / bitwidth.
  adc_oneshot_chan_cfg_t chan_cfg = {};
  chan_cfg.atten    = config_.atten;
  chan_cfg.bitwidth = config_.bitwidth;
  if (adc_oneshot_config_channel(adc_handle_, vout_channel_, &chan_cfg) != ESP_OK ||
      adc_oneshot_config_channel(adc_handle_, vref_channel_, &chan_cfg) != ESP_OK) {
    ESP_LOGE(kTag, "adc_oneshot_config_channel failed.");
    Deinit();
    return false;
  }

  // Per-channel curve-fitting calibration (ESP32-S3). If unavailable, fall back to raw counts.
  adc_cali_curve_fitting_config_t cali_cfg = {};
  cali_cfg.unit_id  = adc_unit_;
  cali_cfg.atten    = config_.atten;
  cali_cfg.bitwidth = config_.bitwidth;
  cali_cfg.chan     = vout_channel_;
  bool vout_cali_ok = (adc_cali_create_scheme_curve_fitting(&cali_cfg, &vout_cali_handle_) == ESP_OK);
  cali_cfg.chan     = vref_channel_;
  bool vref_cali_ok = (adc_cali_create_scheme_curve_fitting(&cali_cfg, &vref_cali_handle_) == ESP_OK);
  cali_enabled_ = vout_cali_ok && vref_cali_ok;
  if (!cali_enabled_) {
    ESP_LOGW(kTag, "ADC calibration unavailable; using raw-count approximation.");
    if (vout_cali_handle_) {
      adc_cali_delete_scheme_curve_fitting(vout_cali_handle_);
      vout_cali_handle_ = nullptr;
    }
    if (vref_cali_handle_) {
      adc_cali_delete_scheme_curve_fitting(vref_cali_handle_);
      vref_cali_handle_ = nullptr;
    }
  }

  ESP_LOGI(kTag, "Initialized (ADC unit %d, VOUT ch%d GPIO%d, VREF ch%d GPIO%d, cali %s).", adc_unit_,
           vout_channel_, config_.vout_pin, vref_channel_, config_.vref_pin,
           cali_enabled_ ? "on" : "off");
  return true;
}

bool CoSensor::Deinit() {
  if (adc_handle_ == nullptr) {
    return true;
  }
  if (vout_cali_handle_) {
    adc_cali_delete_scheme_curve_fitting(vout_cali_handle_);
    vout_cali_handle_ = nullptr;
  }
  if (vref_cali_handle_) {
    adc_cali_delete_scheme_curve_fitting(vref_cali_handle_);
    vref_cali_handle_ = nullptr;
  }
  cali_enabled_ = false;
  adc_oneshot_del_unit(adc_handle_);
  adc_handle_  = nullptr;
  data_valid_  = false;
  ESP_LOGI(kTag, "Deinitialized.");
  return true;
}

bool CoSensor::ReadChannelMv(adc_channel_t channel, adc_cali_handle_t cali, uint16_t* raw_out,
                             int* mv_out) {
  const uint8_t num_samples = config_.samples_per_read == 0 ? 1 : config_.samples_per_read;
  int32_t raw_accum = 0;
  for (uint8_t i = 0; i < num_samples; i++) {
    int raw = 0;
    esp_err_t ret = adc_oneshot_read(adc_handle_, channel, &raw);
    if (ret != ESP_OK) {
      ESP_LOGW(kTag, "adc_oneshot_read(ch%d) failed: %s", channel, esp_err_to_name(ret));
      return false;
    }
    raw_accum += raw;
  }
  int raw_avg = static_cast<int>(raw_accum / num_samples);
  *raw_out = static_cast<uint16_t>(raw_avg);

  if (cali != nullptr) {
    int mv = 0;
    if (adc_cali_raw_to_voltage(cali, raw_avg, &mv) != ESP_OK) {
      return false;
    }
    *mv_out = mv;
  } else {
    // No calibration: approximate mV from raw counts assuming ~1250 mV full-scale at 2.5 dB and a
    // 12-bit result. This is coarse but keeps the sensor functional without calibration data.
    *mv_out = static_cast<int>(raw_avg * 1250 / 4095);
  }
  return true;
}

bool CoSensor::Update() {
  if (adc_handle_ == nullptr) {
    data_valid_ = false;
    return false;
  }

  if (!ReadChannelMv(vout_channel_, vout_cali_handle_, &vout_raw_, &vout_mv_) ||
      !ReadChannelMv(vref_channel_, vref_cali_handle_, &vref_raw_, &vref_mv_)) {
    data_valid_ = false;
    return false;
  }

  // ppm = (V_out_mV - V_ref_mV)/1000 * 1e9 / (R_f * sensitivity_nA_per_ppm). The VOUT-VREF subtraction
  // removes the bias, leaving the signal voltage proportional to CO concentration.
  const float signal_mv = static_cast<float>(vout_mv_ - vref_mv_);
  float ppm = signal_mv / 1000.0f * 1.0e9f / (config_.r_f_ohms * config_.sensitivity_na_per_ppm);
  if (ppm < 0.0f) {
    ppm = 0.0f;  // Clamp noise below zero-CO to 0.
  }

  // EMA smoothing (seeded on the first reading so it doesn't ramp from 0).
  if (config_.ema_alpha > 0.0f && co_ppm_seeded_) {
    co_ppm_ = co_ppm_ + config_.ema_alpha * (ppm - co_ppm_);
  } else {
    co_ppm_ = ppm;
    co_ppm_seeded_ = true;
  }

  data_valid_ = true;
  return true;
}
