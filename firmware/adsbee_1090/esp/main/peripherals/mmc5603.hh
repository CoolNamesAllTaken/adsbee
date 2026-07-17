#pragma once

#include <cstdint>
#include "driver/gpio.h"
#include "driver/i2c_master.h"
#include "esp_err.h"
#include "bsp.hh"
#include "glm/glm.hpp"  // glm::vec3

// MMC5603NJ 3-Axis Magnetometer Driver
// Datasheet: https://www.memsic.com/Public/Uploads/uploadfile/files/20220119/MMC5603NJDatasheetRev.B.pdf

class Mmc5603 {
 public:
  // I2C address (fixed)
  static constexpr uint8_t kI2cAddress = 0x30;

  // -------------------------------------------------------------------------
  // Register addresses
  // -------------------------------------------------------------------------
  static constexpr uint8_t kRegXout0  = 0x00;  // Xout[19:12]
  static constexpr uint8_t kRegXout1  = 0x01;  // Xout[11:4]
  static constexpr uint8_t kRegYout0  = 0x02;  // Yout[19:12]
  static constexpr uint8_t kRegYout1  = 0x03;  // Yout[11:4]
  static constexpr uint8_t kRegZout0  = 0x04;  // Zout[19:12]
  static constexpr uint8_t kRegZout1  = 0x05;  // Zout[11:4]
  static constexpr uint8_t kRegXout2  = 0x06;  // Xout[3:0] in bits [7:4]
  static constexpr uint8_t kRegYout2  = 0x07;  // Yout[3:0] in bits [7:4]
  static constexpr uint8_t kRegZout2  = 0x08;  // Zout[3:0] in bits [7:4]
  static constexpr uint8_t kRegStatus = 0x18;  // Status register
  static constexpr uint8_t kRegOdr    = 0x1A;  // Output data rate (continuous mode)
  static constexpr uint8_t kRegCtrl0  = 0x1B;  // Control register 0
  static constexpr uint8_t kRegCtrl1  = 0x1C;  // Control register 1 (BW, SET/RESET)
  static constexpr uint8_t kRegCtrl2  = 0x1D;  // Control register 2 (continuous mode)
  static constexpr uint8_t kRegProdId = 0x39;  // Product ID (reads 0x10)

  // -------------------------------------------------------------------------
  // Status register bit masks
  // -------------------------------------------------------------------------
  static constexpr uint8_t kStatusMeasMDone = (1 << 6);  // Mag measurement done

  // -------------------------------------------------------------------------
  // Control register 0 bit masks
  // -------------------------------------------------------------------------
  static constexpr uint8_t kCtrl0TakeMeasM  = (1 << 0);  // Take magnetic measurement
  static constexpr uint8_t kCtrl0StartMdt   = (1 << 2);  // Start MDT (factory)
  static constexpr uint8_t kCtrl0DoSet      = (1 << 3);  // Perform SET
  static constexpr uint8_t kCtrl0DoReset    = (1 << 4);  // Perform RESET
  static constexpr uint8_t kCtrl0AutoSrEn   = (1 << 5);  // Enable auto SET/RESET
  static constexpr uint8_t kCtrl0CmmFreqEn  = (1 << 7);  // Enable continuous mode freq

  // -------------------------------------------------------------------------
  // Control register 1 bit masks (bandwidth)
  // -------------------------------------------------------------------------
  static constexpr uint8_t kCtrl1Bw00   = 0x00;  // 75 Hz max ODR,  1.5 mG RMS noise
  static constexpr uint8_t kCtrl1Bw01   = 0x01;  // 150 Hz max ODR, 2.0 mG RMS noise
  static constexpr uint8_t kCtrl1Bw10   = 0x02;  // 255 Hz max ODR, 3.0 mG RMS noise
  static constexpr uint8_t kCtrl1Bw11   = 0x03;  // 1000 Hz max ODR, 4.0 mG RMS noise
  static constexpr uint8_t kCtrl1SwReset = (1 << 7);  // Software reset

  // -------------------------------------------------------------------------
  // Control register 2 bit masks
  // -------------------------------------------------------------------------
  static constexpr uint8_t kCtrl2PrdSetMask = 0x07;   // Prd_set[2:0]: samples per auto-SET
  static constexpr uint8_t kCtrl2EnPrdSet   = (1 << 3);  // Enable periodic SET
  static constexpr uint8_t kCtrl2CmmEn      = (1 << 4);  // Enable continuous mode
  static constexpr uint8_t kCtrl2HiPower    = (1 << 7);  // Enable 1000 Hz mode

  // Prd_set[2:0] encodings: one automatic SET every N samples (datasheet p.10).
  static constexpr uint8_t kPrdSet1    = 0;  // every 1 sample
  static constexpr uint8_t kPrdSet25   = 1;  // every 25
  static constexpr uint8_t kPrdSet75   = 2;  // every 75
  static constexpr uint8_t kPrdSet100  = 3;  // every 100
  static constexpr uint8_t kPrdSet250  = 4;  // every 250
  static constexpr uint8_t kPrdSet500  = 5;  // every 500
  static constexpr uint8_t kPrdSet1000 = 6;  // every 1000
  static constexpr uint8_t kPrdSet2000 = 7;  // every 2000

  // -------------------------------------------------------------------------
  // Sensor constants
  // -------------------------------------------------------------------------
  // 20-bit mode: null field output = 524288 counts (2^19), sensitivity = 16384 counts/G
  static constexpr uint32_t kNullFieldCounts = 524288;
  static constexpr float    kCountsPerGauss  = 16384.0f;
  static constexpr float    kGaussToUt       = 100.0f;    // 1 G = 100 µT
  static constexpr uint8_t  kExpectedChipId  = 0x10;

  // -------------------------------------------------------------------------
  // Timing constants (ms)
  // -------------------------------------------------------------------------
  static constexpr uint32_t kStartupTimeMs    = 20;  // Power-on / soft-reset time
  static constexpr uint32_t kSetResetTimeMs   = 1;   // SET/RESET settling time
  static constexpr uint32_t kMeasurementMaxMs = 15;  // Max single-shot measurement

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

    // I2C clock speed for this device (Hz). Max 400 kHz per datasheet.
    uint32_t i2c_speed_hz = 400000;

    // Bandwidth selection (BW<1:0>). Controls noise / max ODR trade-off.
    // Use kCtrl1Bw00 (75 Hz, lowest noise) for typical compass applications.
    uint8_t bandwidth = kCtrl1Bw00;

    // Continuous-mode output data rate (ODR[7:0]). MUST be non-zero to enter
    // continuous mode. With BW00 the max ODR is 75 Hz; 50 Hz is plenty for a
    // compass and keeps headroom.
    uint8_t odr_hz = 50;

    // Periodic automatic SET. In continuous mode the part performs a SET every
    // Prd_set samples (requires Auto_SR + En_prd_set), which removes the bridge
    // offset that drifts with temperature — without this the readings carry an
    // uncompensated, drifting bias. kPrdSet100 = one SET per 100 samples.
    bool    auto_set_reset = true;
    uint8_t prd_set        = kPrdSet100;
  };

  Mmc5603() : Mmc5603(Config{}) {}
  explicit Mmc5603(const Config& config);
  ~Mmc5603();

  Mmc5603(const Mmc5603&)            = delete;
  Mmc5603& operator=(const Mmc5603&) = delete;

  // -------------------------------------------------------------------------
  // Lifecycle
  // -------------------------------------------------------------------------

  // Registers the device on the bus, verifies the product ID, performs an
  // initial SET operation, and triggers the first measurement.
  bool Init();

  // Removes the device from the bus and releases handles owned by this driver.
  // Measurement data is preserved. The driver may be re-initialised via Init().
  bool Deinit();

  bool IsInitialized() const { return i2c_handle_ != nullptr; }

  // -------------------------------------------------------------------------
  // Sensor control (call only after Init())
  // -------------------------------------------------------------------------

  // Non-blocking update. State machine:
  //   - No pending measurement → triggers one and returns immediately.
  //   - Pending measurement, still busy → returns without touching values.
  //   - Pending measurement, data ready → reads result, then triggers the
  //     next measurement immediately before returning.
  bool Update();

  // Issues a software reset and re-runs Init().
  bool SoftReset();

  // Starts a non-blocking single-shot magnetic measurement.
  bool TriggerMeasurement();

  // Returns true when the conversion whose done-bit is `done_mask` is complete.
  // Sets *ready on success; returns false on bus error.
  bool IsMeasurementReady(uint8_t done_mask, bool* ready);

  // Reads and decodes the 20-bit XYZ output. Call only after the magnetic
  // measurement's done-bit is set.
  bool ReadMeasurement();

  // -------------------------------------------------------------------------
  // Getters — always safe to call; return the last successfully read values.
  // -------------------------------------------------------------------------
  float GetMagneticFieldXGauss() const { return mag_x_gauss_; }
  float GetMagneticFieldYGauss() const { return mag_y_gauss_; }
  float GetMagneticFieldZGauss() const { return mag_z_gauss_; }
  float GetMagneticFieldXUt()    const { return mag_x_gauss_ * kGaussToUt; }
  float GetMagneticFieldYUt()    const { return mag_y_gauss_ * kGaussToUt; }
  float GetMagneticFieldZUt()    const { return mag_z_gauss_ * kGaussToUt; }
  glm::vec3 GetMagneticFieldGauss() const {
    return glm::vec3(mag_x_gauss_, mag_y_gauss_, mag_z_gauss_);
  }

 private:
  esp_err_t WriteReg(uint8_t reg, uint8_t value);
  esp_err_t ReadRegs(uint8_t start_reg, uint8_t* buf, size_t len);
  esp_err_t PerformSet();
  // Verifies chip ID, configures registers, and triggers the first measurement.
  // Called by both Init() and SoftReset() once an I2C handle is available.
  bool Configure();

  const Config             config_;
  i2c_master_dev_handle_t  i2c_handle_          = nullptr;
  i2c_master_bus_handle_t  owned_bus_handle_     = nullptr;

  float mag_x_gauss_ = 0.0f;
  float mag_y_gauss_ = 0.0f;
  float mag_z_gauss_ = 0.0f;
};
