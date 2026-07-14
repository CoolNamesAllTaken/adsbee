#pragma once

#include <cstdint>
#include "driver/i2c_master.h"
#include "driver/gpio.h"
#include "esp_err.h"
#include "bsp.hh"

// LTR-329 Ambient Light Sensor Driver
// Datasheet: https://optoelectronics.liteon.com/upload/download/DS86-2013-0003/LTR-329ALS-01_DS_V1.pdf

class Ltr329 {
 public:
  // I2C address (fixed, no alternate)
  static constexpr uint8_t kI2cAddress = 0x29;

  // -------------------------------------------------------------------------
  // Register Map
  // -------------------------------------------------------------------------
  enum Register : uint8_t {
    kRegAlsContr    = 0x80,  // ALS control
    kRegAlsMeasRate = 0x85,  // ALS measurement rate
    kRegPartId      = 0x86,  // Part ID / revision
    kRegManufacId   = 0x87,  // Manufacturer ID
    kRegAlsDataCh1L = 0x88,  // ALS CH1 data low byte
    kRegAlsDataCh1H = 0x89,  // ALS CH1 data high byte
    kRegAlsDataCh0L = 0x8A,  // ALS CH0 data low byte
    kRegAlsDataCh0H = 0x8B,  // ALS CH0 data high byte
    kRegAlsStatus   = 0x8C,  // ALS status
  };

  // -------------------------------------------------------------------------
  // ALS_CONTR (0x80) — Gain
  // -------------------------------------------------------------------------
  enum class Gain : uint8_t {
    kGain1x  = 0x00,  // 1 lux to 64k lux (default)
    kGain2x  = 0x01,  // 0.5 lux to 32k lux
    kGain4x  = 0x02,  // 0.25 lux to 16k lux
    kGain8x  = 0x03,  // 0.125 lux to 8k lux
    kGain48x = 0x06,  // 0.02 lux to 1.3k lux
    kGain96x = 0x07,  // 0.01 lux to 600 lux
  };

  // -------------------------------------------------------------------------
  // ALS_MEAS_RATE (0x85) — Integration time & repeat rate
  // -------------------------------------------------------------------------
  enum class IntegrationTime : uint8_t {
    kTime100ms = 0x00,  // 100ms (default)
    kTime50ms  = 0x01,  // 50ms
    kTime200ms = 0x02,  // 200ms
    kTime400ms = 0x03,  // 400ms
    kTime150ms = 0x04,  // 150ms
    kTime250ms = 0x05,  // 250ms
    kTime300ms = 0x06,  // 300ms
    kTime350ms = 0x07,  // 350ms
  };

  enum class MeasurementRate : uint8_t {
    kRate50ms   = 0x00,  // 50ms
    kRate100ms  = 0x01,  // 100ms
    kRate200ms  = 0x02,  // 200ms (default)
    kRate500ms  = 0x03,  // 500ms
    kRate1000ms = 0x04,  // 1000ms
    kRate2000ms = 0x05,  // 2000ms
  };

  // -------------------------------------------------------------------------
  // ALS_STATUS (0x8C) bit masks
  // -------------------------------------------------------------------------
  static constexpr uint8_t kStatusDataValid  = (1 << 7);
  static constexpr uint8_t kStatusDataNew    = (1 << 2);
  static constexpr uint8_t kStatusGainMask   = 0x70;
  static constexpr uint8_t kStatusGainShift  = 4;

  // -------------------------------------------------------------------------
  // ALS_CONTR (0x80) bit masks
  // -------------------------------------------------------------------------
  static constexpr uint8_t kContrGainMask   = 0x1C;
  static constexpr uint8_t kContrGainShift  = 2;
  static constexpr uint8_t kContrSwReset    = (1 << 1);
  static constexpr uint8_t kContrAlsMode    = (1 << 0);  // 1 = active mode

  // Part / manufacturer identity
  static constexpr uint8_t kPartIdMask     = 0xF0;
  static constexpr uint8_t kExpectedPartId = 0xA0;
  static constexpr uint8_t kManufacturerId = 0x05;

  // -------------------------------------------------------------------------
  // Configuration — passed to the constructor.
  // -------------------------------------------------------------------------
  struct Config {
    // I2C bus configuration. Init() calls i2c_master_get_bus_handle() first;
    // if the port already has a bus (created by another driver) the existing
    // handle is reused and no new bus is created. If the port is unclaimed,
    // the driver creates and owns the bus and tears it down in Deinit().
    i2c_port_num_t i2c_port  = bsp.periph_i2c_port;
    gpio_num_t     sda_pin   = bsp.periph_i2c_sda_pin;
    gpio_num_t     scl_pin   = bsp.periph_i2c_scl_pin;

    // I2C clock speed for this device (Hz).
    uint32_t i2c_speed_hz = 400000;

    // Sensor settings applied during Init().
    Gain            gain             = Gain::kGain1x;
    IntegrationTime integration_time = IntegrationTime::kTime50ms;
    MeasurementRate measurement_rate = MeasurementRate::kRate50ms;

    // Ambient-level normalization (see GetAmbientLevel()). Lux is mapped to a
    // 0..1 level on a log scale between [lux_min, lux_max], then EMA-smoothed.
    float lux_min   = 5.0f;     // lux at/below -> ambient level 0 (darkest)
    float lux_max   = 5000.0f;  // lux at/above -> ambient level 1 (brightest)
    float ema_alpha = 0.01f;    // smoothing factor: higher = snappier
  };

  // No-argument default constructor — uses all Config defaults.
  Ltr329() : Ltr329(Config{}) {}

  // Constructs the driver, storing the config. No I2C transactions occur here.
  explicit Ltr329(const Config& config);

  // Destructor — calls Deinit() automatically if still initialised.
  ~Ltr329();

  // Non-copyable, non-movable (owns an I2C device handle).
  Ltr329(const Ltr329&)            = delete;
  Ltr329& operator=(const Ltr329&) = delete;

  // ---------------------------------------------------------------------------
  // Lifecycle
  // ---------------------------------------------------------------------------

  // Registers the device on the bus, verifies device identity, performs a
  // soft-reset, applies the config settings, and enters active measurement
  // mode. Safe to call again after a successful Deinit().
  bool Init();

  // Removes the device from the bus and releases handles owned by this driver.
  // Measurement data is preserved. The driver may be re-initialised via
  // Init() at any time after this call.
  bool Deinit();

  // Returns true after a successful Init() and before Deinit() is called.
  bool IsInitialized() const { return i2c_handle_ != nullptr; }

  // ---------------------------------------------------------------------------
  // Sensor control (call only after Init())
  // ---------------------------------------------------------------------------

  // Reads the latest ALS channels into internal state. Returns true when new
  // data was available and decoded; false on bus error or no new data yet.
  bool Update();

  // Issues a soft reset (sensor returns to standby; re-apply SetActiveMode()
  // or call Init() again to resume measurements).
  bool SoftReset();

  // Changes the ALS gain at runtime.
  bool SetGain(Gain gain);

  // Changes integration time and measurement repeat rate at runtime.
  bool SetMeasurementConfig(IntegrationTime integration_time,
                             MeasurementRate measurement_rate);

  // Puts the device into continuous measurement (active) mode.
  bool SetActiveMode();

  // Puts the device into standby (low-power) mode.
  bool SetStandbyMode();

  // ---------------------------------------------------------------------------
  // Getters — always safe to call; return the last successfully read values.
  // ---------------------------------------------------------------------------
  uint16_t GetCh0Raw()   const { return ch0_raw_; }    // Visible + IR counts
  uint16_t GetCh1Raw()   const { return ch1_raw_; }    // IR-only counts
  float    GetLux()      const { return lux_; }         // Computed lux
  bool     IsDataValid() const { return data_valid_; }  // True when data is fresh

  // Normalized, EMA-smoothed ambient light level in [0, 1] (0 = dark, 1 =
  // bright), derived from the lux reading via a log-scale map between the
  // Config lux_min/lux_max. Updated in Update(); intended to drive display
  // front-light and status-LED auto-brightness. Always safe to call.
  float    GetAmbientLevel() const { return ambient_level_; }

 private:
  esp_err_t WriteRegister(Register reg, uint8_t value);
  esp_err_t ReadRegister(Register reg, uint8_t* value);
  esp_err_t ReadRegisters(Register start_reg, uint8_t* buf, size_t len);
  float     ComputeLux(uint16_t ch0, uint16_t ch1);

  // Immutable configuration stored at construction time.
  const Config config_;

  // Device handle — allocated by Init(), released by Deinit().
  i2c_master_dev_handle_t i2c_handle_ = nullptr;

  // Non-null only when we created the bus ourselves; null when we reused one
  // that was already initialized by another driver on the same port.
  i2c_master_bus_handle_t owned_bus_handle_ = nullptr;

  // Shadow of current register settings (updated by setters).
  Gain            current_gain_             = Gain::kGain1x;
  IntegrationTime current_integration_time_ = IntegrationTime::kTime100ms;

  // Updates ambient_level_ from the current lux_ (log-normalize + EMA smooth).
  void UpdateAmbientLevel();

  // Last successfully decoded measurement values.
  uint16_t ch0_raw_    = 0;
  uint16_t ch1_raw_    = 0;
  float    lux_        = 0.0f;
  bool     data_valid_ = false;

  // Normalized ambient light level in [0, 1], EMA-smoothed. Seeded on the first
  // valid reading so it doesn't ramp up from 0 on boot.
  float    ambient_level_        = 0.0f;
  bool     ambient_level_seeded_ = false;
};
