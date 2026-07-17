#pragma once

#include <cstdint>
#include "driver/gpio.h"
#include "driver/i2c_master.h"
#include "esp_err.h"
#include "bsp.hh"

// AHT20 Temperature & Humidity Sensor Driver
// Datasheet: https://asairsensors.com/wp-content/uploads/2021/09/Data-Sheet-AHT20-ASAIR-V1.0.03.pdf

class Aht20 {
 public:
  // I2C address (fixed, no alternate)
  static constexpr uint8_t kI2cAddress = 0x38;

  // -------------------------------------------------------------------------
  // Command bytes
  // -------------------------------------------------------------------------
  static constexpr uint8_t kCmdInitialize     = 0xBE;  // Calibrate / initialise
  static constexpr uint8_t kCmdTriggerMeasure = 0xAC;  // Start measurement
  static constexpr uint8_t kCmdSoftReset      = 0xBA;  // Soft reset
  static constexpr uint8_t kCmdGetStatus      = 0x71;  // Read status byte

  // Fixed parameter bytes required by the AHT20 protocol.
  static constexpr uint8_t kMeasureParam1 = 0x33;
  static constexpr uint8_t kMeasureParam2 = 0x00;
  static constexpr uint8_t kInitParam1    = 0x08;
  static constexpr uint8_t kInitParam2    = 0x00;

  // -------------------------------------------------------------------------
  // Status byte bit masks
  // -------------------------------------------------------------------------
  static constexpr uint8_t kStatusBusy       = (1 << 7);  // 1 = busy measuring
  static constexpr uint8_t kStatusCalibrated = (1 << 3);  // 1 = calibrated

  // -------------------------------------------------------------------------
  // Timing constants (ms)
  // -------------------------------------------------------------------------
  static constexpr uint32_t kStartupTimeMs     = 40;  // After power-on
  static constexpr uint32_t kMeasurementTimeMs = 80;  // Max measurement duration
  static constexpr uint32_t kSoftResetTimeMs   = 20;  // After soft reset

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
    // The AHT20 supports Standard (100 kHz) and Fast (400 kHz) modes.
    uint32_t i2c_speed_hz = 400000;
  };

  Aht20() : Aht20(Config{}) {}
  explicit Aht20(const Config& config);
  ~Aht20();

  Aht20(const Aht20&)            = delete;
  Aht20& operator=(const Aht20&) = delete;

  // ---------------------------------------------------------------------------
  // Lifecycle
  // ---------------------------------------------------------------------------

  // Registers the device on the bus, waits for sensor startup, and ensures
  // the internal calibration is complete. Safe to call again after Deinit().
  bool Init();

  // Removes the device from the bus and releases handles owned by this driver.
  // Measurement data is preserved. The driver may be re-initialised via Init().
  bool Deinit();

  bool IsInitialized() const { return i2c_handle_ != nullptr; }

  // ---------------------------------------------------------------------------
  // Sensor control (call only after Init())
  // ---------------------------------------------------------------------------

  // Non-blocking update. State machine:
  //   - No pending measurement → triggers one and returns immediately.
  //   - Pending measurement, still busy → returns without touching values.
  //   - Pending measurement, data ready → reads result, then triggers the
  //     next measurement immediately before returning.
  bool Update();

  // Issues a soft reset; automatically re-runs calibration afterwards.
  bool SoftReset();

  // Starts a non-blocking measurement. Poll IsBusy(), then call
  // ReadMeasurement() once it returns false.
  bool TriggerMeasurement();

  // Checks the busy flag. Sets *busy = true while a measurement is running.
  // Returns false on bus error.
  bool IsBusy(bool* busy);

  // Reads and decodes measurement data. Call only after IsBusy() → false.
  bool ReadMeasurement();

  // ---------------------------------------------------------------------------
  // Getters — always safe to call; return the last successfully read values.
  // ---------------------------------------------------------------------------
  float GetTemperatureCelsius()    const { return temperature_c_; }
  float GetTemperatureFahrenheit() const { return temperature_c_ * 9.0f / 5.0f + 32.0f; }
  float GetRelativeHumidity()      const { return humidity_rh_; }
  bool  IsCalibrated()             const { return calibrated_; }

 private:
  esp_err_t ReadStatus(uint8_t* status);
  bool      EnsureCalibrated();

  const Config             config_;
  i2c_master_dev_handle_t  i2c_handle_          = nullptr;
  i2c_master_bus_handle_t  owned_bus_handle_     = nullptr;

  float temperature_c_      = 0.0f;
  float humidity_rh_        = 0.0f;
  bool  calibrated_         = false;
  bool  measurement_pending_ = false;
};
