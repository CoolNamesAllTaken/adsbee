#pragma once

#include <cstdint>
#include "driver/gpio.h"
#include "esp_adc/adc_cali.h"
#include "esp_adc/adc_oneshot.h"
#include "esp_err.h"
#include "bsp.hh"

// CO (carbon monoxide) analog sensor driver.
//
// The sensor is an electrochemical cell with a transimpedance front-end read via two ESP32-S3 ADC1
// inputs: CO_VOUT (signal + bias) and CO_VREF (bias only). The differential (VOUT - VREF) removes the
// bias and is proportional to CO concentration:
//   V_out = R_f * sensitivity * ppm / 1e9 + V_bias          (forward model)
//   ppm   = (V_out_mV - V_ref_mV) / 1000 * 1e9 / (R_f * sensitivity_nA_per_ppm)
// with R_f = 100 kOhm, sensitivity = 1.5 nA/ppm, V_bias = 0.16 V carried on CO_VREF. Example: at
// 5000 ppm, V_out ~= 0.91 V, VOUT-VREF ~= 0.75 V, staying within the ~1.25 V ADC ceiling at 2.5 dB.
//
// The ADC unit/channel are derived from the GPIO number at Init() via adc_oneshot_io_to_channel, so
// only the two GPIO pins need to be configured. Follows the same lifecycle as the I2C sensor drivers
// (Init/Deinit/IsInitialized/Update + cached getters), but owns an ADC oneshot unit instead of an
// I2C device handle.
class CoSensor {
 public:
  // -------------------------------------------------------------------------
  // Configuration — passed to the constructor.
  // -------------------------------------------------------------------------
  struct Config {
    // ADC inputs (GPIO numbers). The ADC unit + channel are resolved from these at Init().
    gpio_num_t vout_pin = bsp.co_vout_pin;
    gpio_num_t vref_pin = bsp.co_vref_pin;

    // ADC channel settings. 2.5 dB attenuation (~1250 mV full-scale) gives the best accuracy for the
    // ~0.91 V max signal per the sensor design notes.
    adc_atten_t    atten    = ADC_ATTEN_DB_2_5;
    adc_bitwidth_t bitwidth = ADC_BITWIDTH_DEFAULT;

    // Number of raw samples averaged per channel per Update() (simple noise reduction).
    uint8_t samples_per_read = 8;

    // Transimpedance / sensor conversion constants (see the class comment). Kept configurable so the
    // scale can be trimmed against a calibrated reference.
    float r_f_ohms             = 100000.0f;  // feedback resistor
    float sensitivity_na_per_ppm = 1.5f;     // sensor output current per ppm
    // V_bias (0.16 V) is provided physically on CO_VREF, so it does not appear here; it is removed by
    // the VOUT-VREF subtraction.

    // EMA smoothing factor for the ppm output: higher = snappier. 0 disables smoothing.
    float ema_alpha = 0.1f;
  };

  // No-argument default constructor — uses all Config defaults.
  CoSensor() : CoSensor(Config{}) {}

  // Constructs the driver, storing the config. No ADC operations occur here.
  explicit CoSensor(const Config& config);

  // Destructor — calls Deinit() automatically if still initialised.
  ~CoSensor();

  // Non-copyable, non-movable (owns ADC handles).
  CoSensor(const CoSensor&)            = delete;
  CoSensor& operator=(const CoSensor&) = delete;

  // ---------------------------------------------------------------------------
  // Lifecycle
  // ---------------------------------------------------------------------------

  // Resolves the ADC unit/channels from the configured GPIOs, brings up the ADC oneshot unit,
  // configures both channels, and sets up per-channel calibration (curve fitting on ESP32-S3; falls
  // back to a raw approximation if calibration is unavailable). Returns false on any failure.
  bool Init();

  // Releases the ADC unit and calibration handles owned by this driver. Idempotent.
  bool Deinit();

  // Returns true after a successful Init() and before Deinit() is called.
  bool IsInitialized() const { return adc_handle_ != nullptr; }

  // ---------------------------------------------------------------------------
  // Sensor control (call only after Init())
  // ---------------------------------------------------------------------------

  // Reads both ADC channels, converts to millivolts, and computes CO ppm. Returns false on ADC error.
  bool Update();

  // ---------------------------------------------------------------------------
  // Getters — always safe to call; return the last successfully read values.
  // ---------------------------------------------------------------------------
  uint16_t GetVoutRaw()   const { return vout_raw_; }
  uint16_t GetVrefRaw()   const { return vref_raw_; }
  int      GetVoutMv()    const { return vout_mv_; }
  int      GetVrefMv()    const { return vref_mv_; }
  float    GetCoPpm()     const { return co_ppm_; }
  bool     IsDataValid()  const { return data_valid_; }

 private:
  // Reads one channel, averaging config_.samples_per_read raw samples, and converts to mV. Returns
  // false on ADC error.
  bool ReadChannelMv(adc_channel_t channel, adc_cali_handle_t cali, uint16_t* raw_out, int* mv_out);

  // Immutable configuration stored at construction time.
  const Config config_;

  // ADC oneshot unit handle — allocated by Init(), released by Deinit().
  adc_oneshot_unit_handle_t adc_handle_ = nullptr;

  // Resolved from the configured GPIOs at Init().
  adc_unit_t    adc_unit_     = ADC_UNIT_1;
  adc_channel_t vout_channel_ = ADC_CHANNEL_0;
  adc_channel_t vref_channel_ = ADC_CHANNEL_1;

  // Per-channel calibration handles (curve fitting). Null when calibration is unavailable.
  adc_cali_handle_t vout_cali_handle_ = nullptr;
  adc_cali_handle_t vref_cali_handle_ = nullptr;
  bool              cali_enabled_     = false;

  // Last successfully decoded measurement values.
  uint16_t vout_raw_ = 0;
  uint16_t vref_raw_ = 0;
  int      vout_mv_  = 0;
  int      vref_mv_  = 0;
  float    co_ppm_   = 0.0f;
  bool     data_valid_ = false;

  // EMA state for the ppm output; seeded on the first valid reading.
  bool co_ppm_seeded_ = false;
};
