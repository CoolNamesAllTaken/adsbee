#pragma once

#include <cstdint>
#include "driver/i2c_master.h"
#include "driver/gpio.h"
#include "esp_err.h"
#include "bsp.hh"

// SPL06-003 Digital Barometric Pressure Sensor Driver
// Datasheet: https://www.gotronic.fr/pj2-spl06-003-datasheet-2.pdf

class Spl06003 {
 public:
  // I2C addresses (selected by SDO pin level)
  static constexpr uint8_t kI2cAddressPrimary   = 0x77;  // SDO high
  static constexpr uint8_t kI2cAddressSecondary = 0x76;  // SDO low

  // -------------------------------------------------------------------------
  // Register Map
  // -------------------------------------------------------------------------
  enum Register : uint8_t {
    kRegPsrB2       = 0x00,  // Pressure MSB
    kRegPsrB1       = 0x01,
    kRegPsrB0       = 0x02,  // Pressure LSB
    kRegTmpB2       = 0x03,  // Temperature MSB
    kRegTmpB1       = 0x04,
    kRegTmpB0       = 0x05,  // Temperature LSB
    kRegPrsCfg      = 0x06,  // Pressure configuration
    kRegTmpCfg      = 0x07,  // Temperature configuration
    kRegMeasCfg     = 0x08,  // Measurement mode control
    kRegCfgReg      = 0x09,  // Interrupt and FIFO configuration
    kRegIntSts      = 0x0A,  // Interrupt status (read-only)
    kRegFifoSts     = 0x0B,  // FIFO status (read-only)
    kRegReset       = 0x0C,  // Soft-reset / FIFO flush
    kRegProductId   = 0x0D,  // Product and revision ID
    kRegCoefStart   = 0x10,  // First calibration coefficient register (18 bytes)
    kRegTmpCoefSrce = 0x28,  // Temperature coefficient source
  };

  // -------------------------------------------------------------------------
  // PRS_CFG (0x06) — Pressure oversampling rate (OSR)
  // -------------------------------------------------------------------------
  enum class PressureOversamplingRate : uint8_t {
    kOsr1x   = 0x00,  // 1x (lowest noise penalty / fastest, default)
    kOsr2x   = 0x01,
    kOsr4x   = 0x02,
    kOsr8x   = 0x03,
    kOsr16x  = 0x04,
    kOsr32x  = 0x05,
    kOsr64x  = 0x06,
    kOsr128x = 0x07,  // Highest resolution (requires bit-shift)
  };

  // PRS_CFG — Pressure measurement rate
  enum class PressureMeasurementRate : uint8_t {
    kRate1Hz   = 0x00,
    kRate2Hz   = 0x01,
    kRate4Hz   = 0x02,
    kRate8Hz   = 0x03,
    kRate16Hz  = 0x04,
    kRate32Hz  = 0x05,
    kRate64Hz  = 0x06,
    kRate128Hz = 0x07,
  };

  // -------------------------------------------------------------------------
  // TMP_CFG (0x07) — Temperature oversampling rate
  // -------------------------------------------------------------------------
  enum class TemperatureOversamplingRate : uint8_t {
    kOsr1x   = 0x00,
    kOsr2x   = 0x01,
    kOsr4x   = 0x02,
    kOsr8x   = 0x03,
    kOsr16x  = 0x04,
    kOsr32x  = 0x05,
    kOsr64x  = 0x06,
    kOsr128x = 0x07,
  };

  // TMP_CFG — Temperature measurement rate
  enum class TemperatureMeasurementRate : uint8_t {
    kRate1Hz   = 0x00,
    kRate2Hz   = 0x01,
    kRate4Hz   = 0x02,
    kRate8Hz   = 0x03,
    kRate16Hz  = 0x04,
    kRate32Hz  = 0x05,
    kRate64Hz  = 0x06,
    kRate128Hz = 0x07,
  };

  // TMP_CFG — Temperature sensor source
  enum class TemperatureSource : uint8_t {
    kInternal = 0x00,  // ASIC internal temperature sensor
    kExternal = 0x01,  // External MEMS element (recommended for accuracy)
  };

  // -------------------------------------------------------------------------
  // MEAS_CFG (0x08) — Measurement mode
  // -------------------------------------------------------------------------
  enum class MeasurementMode : uint8_t {
    kStandby              = 0x00,  // Idle / low power
    kPressureOnce         = 0x01,  // Single pressure measurement
    kTemperatureOnce      = 0x02,  // Single temperature measurement
    kContinuousPressure   = 0x05,  // Continuous pressure only
    kContinuousTemperature = 0x06, // Continuous temperature only
    kContinuousBoth       = 0x07,  // Continuous pressure + temperature
  };

  // -------------------------------------------------------------------------
  // MEAS_CFG status bit masks (read-only upper nibble)
  // -------------------------------------------------------------------------
  static constexpr uint8_t kMeasCfgCoefRdy   = (1 << 7);  // Coefficients ready
  static constexpr uint8_t kMeasCfgSensorRdy = (1 << 6);  // Sensor initialised
  static constexpr uint8_t kMeasCfgTmpRdy    = (1 << 5);  // Temperature ready
  static constexpr uint8_t kMeasCfgPrsRdy    = (1 << 4);  // Pressure ready

  // -------------------------------------------------------------------------
  // CFG_REG (0x09) bit masks
  // -------------------------------------------------------------------------
  static constexpr uint8_t kCfgIntHlActive = (1 << 7);  // 1 = active-high INT
  static constexpr uint8_t kCfgIntFifo     = (1 << 6);  // FIFO full interrupt
  static constexpr uint8_t kCfgIntTmp      = (1 << 5);  // Temp ready interrupt
  static constexpr uint8_t kCfgIntPrs      = (1 << 4);  // Pressure ready interrupt
  static constexpr uint8_t kCfgTmpShift    = (1 << 3);  // Temp result shift (OSR > 8x)
  static constexpr uint8_t kCfgPrsShift    = (1 << 2);  // Pressure result shift (OSR > 8x)
  static constexpr uint8_t kCfgFifoEn      = (1 << 1);  // FIFO enable
  static constexpr uint8_t kCfgSpiMode     = (1 << 0);  // 3-wire SPI mode

  // -------------------------------------------------------------------------
  // RESET (0x0C) commands
  // -------------------------------------------------------------------------
  static constexpr uint8_t kResetSoftReset = 0x09;  // Full soft-reset + FIFO flush
  static constexpr uint8_t kResetFifoFlush = 0x80;  // FIFO flush only

  // Expected product ID (lower nibble; upper nibble is revision).
  static constexpr uint8_t kProductIdMask     = 0x0F;
  static constexpr uint8_t kExpectedProductId = 0x00;

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

    // I2C address — use kI2cAddressPrimary (0x77) or kI2cAddressSecondary (0x76).
    uint8_t i2c_address = kI2cAddressSecondary;

    // Pressure measurement settings.
    PressureOversamplingRate  pressure_osr  = PressureOversamplingRate::kOsr32x;
    PressureMeasurementRate   pressure_rate = PressureMeasurementRate::kRate128Hz;

    // Temperature measurement settings.
    TemperatureOversamplingRate temperature_osr    = TemperatureOversamplingRate::kOsr32x;
    TemperatureMeasurementRate  temperature_rate   = TemperatureMeasurementRate::kRate128Hz;
    TemperatureSource           temperature_source = TemperatureSource::kInternal;

    // Initial measurement mode entered at the end of Init().
    MeasurementMode measurement_mode = MeasurementMode::kContinuousBoth;

    // Enable result bit-shifting (required when OSR > 8x).
    bool pressure_result_shift    = true;
    bool temperature_result_shift = true;
  };

  // No-argument default constructor — uses all Config defaults.
  Spl06003() : Spl06003(Config{}) {}

  // Constructs the driver, storing the config and zeroing all measurement and
  // calibration state. No I2C transactions occur here.
  explicit Spl06003(const Config& config);

  // Destructor — calls Deinit() automatically if still initialised.
  ~Spl06003();

  // Non-copyable, non-movable (owns an I2C device handle).
  Spl06003(const Spl06003&)            = delete;
  Spl06003& operator=(const Spl06003&) = delete;

  // ---------------------------------------------------------------------------
  // Lifecycle
  // ---------------------------------------------------------------------------

  // Registers the device on the bus, soft-resets, waits for the sensor and
  // coefficients to be ready, reads calibration data, applies the config,
  // and enters the configured measurement mode.
  // Safe to call again after a successful Deinit().
  bool Init();

  // Removes the device from the bus and releases handles owned by this driver.
  // Measurement data and calibration coefficients are preserved.
  // The driver may be re-initialised via Init() at any time after this call.
  bool Deinit();

  // Returns true after a successful Init() and before Deinit() is called.
  bool IsInitialized() const { return i2c_handle_ != nullptr; }

  // ---------------------------------------------------------------------------
  // Sensor control (call only after Init())
  // ---------------------------------------------------------------------------

  // Reads the latest pressure and temperature data into internal state.
  // Returns true on success or when data is not yet ready (not an error).
  // Returns false on bus error.
  bool Update();

  // Issues a soft reset (the device returns to standby and all registers are
  // restored to reset values; calibration coefficients are re-read on Init()).
  bool SoftReset();

  // Change pressure OSR and rate at runtime.
  bool SetPressureConfig(PressureOversamplingRate osr,
                          PressureMeasurementRate rate);

  // Change temperature OSR, rate, and source at runtime.
  bool SetTemperatureConfig(TemperatureOversamplingRate osr,
                             TemperatureMeasurementRate rate,
                             TemperatureSource source);

  // Change measurement mode at runtime.
  bool SetMeasurementMode(MeasurementMode mode);

  // Enable or disable the result bit-shift required for OSR > 8x.
  bool SetResultBitShift(bool enable_pressure_shift,
                          bool enable_temperature_shift);

  // Enable or disable the on-chip FIFO.
  bool SetFifoEnabled(bool enabled);

  // Configure the INT pin behaviour.
  bool SetInterruptConfig(bool active_high, bool fifo_full_int,
                           bool pressure_rdy_int, bool temp_rdy_int);

  // Flush the FIFO without performing a full reset.
  bool FlushFifo();

  // ---------------------------------------------------------------------------
  // Getters — always safe to call; return the last successfully read values.
  // ---------------------------------------------------------------------------
  float GetPressurePa()            const { return pressure_pa_; }
  float GetPressureHpa()           const { return pressure_pa_ / 100.0f; }
  float GetTemperatureCelsius()    const { return temperature_c_; }
  float GetTemperatureFahrenheit() const { return temperature_c_ * 9.0f / 5.0f + 32.0f; }
  // Altitude estimate via the International Standard Atmosphere formula.
  float GetAltitudeMeters(float sea_level_pa = 101325.0f) const;

 private:
  esp_err_t WriteRegister(Register reg, uint8_t value);
  esp_err_t ReadRegister(Register reg, uint8_t* value);
  esp_err_t ReadRegisters(Register start_reg, uint8_t* buf, size_t len);
  esp_err_t ReadCalibrationCoefficients();
  esp_err_t WaitSensorReady();
  bool      ApplyConfig();

  static int32_t TwosComplement24(uint32_t raw);
  static int32_t GetScaleFactor(uint8_t osr);

  // Immutable configuration stored at construction time.
  const Config config_;

  // Device handle — allocated by Init(), released by Deinit().
  i2c_master_dev_handle_t i2c_handle_ = nullptr;

  // Non-null only when we created the bus ourselves; null when we reused one
  // that was already initialized by another driver on the same port.
  i2c_master_bus_handle_t owned_bus_handle_ = nullptr;

  // Current OSR raw values (needed for scale-factor lookup during Update()).
  uint8_t prs_osr_ = 0;
  uint8_t tmp_osr_ = 0;

  // Calibration coefficients (names follow SPL06-003 datasheet notation).
  int32_t c0_  = 0;
  int32_t c1_  = 0;
  int32_t c00_ = 0;
  int32_t c10_ = 0;
  int32_t c01_ = 0;
  int32_t c11_ = 0;
  int32_t c20_ = 0;
  int32_t c21_ = 0;
  int32_t c30_ = 0;

  // Last successfully compensated measurement values.
  float pressure_pa_   = 0.0f;
  float temperature_c_ = 0.0f;
};
