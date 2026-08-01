#include "spa06_003.hh"

#include <cmath>
#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

static const char* kTag = "SPL06003";

// Scale factor table per SPL06-003 datasheet Table 4.
static constexpr int32_t kScaleFactors[] = {
    524288,   // OSR 1x  (0)
    1572864,  // OSR 2x  (1)
    3670016,  // OSR 4x  (2)
    7864320,  // OSR 8x  (3)
    253952,   // OSR 16x (4)
    516096,   // OSR 32x (5)
    1040384,  // OSR 64x (6)
    2088960,  // OSR 128x(7)
};

// ---------------------------------------------------------------------------
// Constructor / Destructor
// ---------------------------------------------------------------------------

Spl06003::Spl06003(const Config& config)
    : config_(config),
      i2c_handle_(nullptr),
      owned_bus_handle_(nullptr),
      prs_osr_(static_cast<uint8_t>(config.pressure_osr)),
      tmp_osr_(static_cast<uint8_t>(config.temperature_osr)),
      c0_(0), c1_(0), c00_(0), c10_(0),
      c01_(0), c11_(0), c20_(0), c21_(0), c30_(0),
      pressure_pa_(0.0f),
      temperature_c_(0.0f) {}

Spl06003::~Spl06003() {
  if (i2c_handle_ != nullptr) {
    Deinit();
  }
}

// ---------------------------------------------------------------------------
// Lifecycle
// ---------------------------------------------------------------------------

bool Spl06003::Init() {
  if (i2c_handle_ != nullptr) {
    ESP_LOGW(kTag, "Already initialized — call Deinit() first");
    return false;
  }

  // Try to claim an already-initialized bus on the configured port.
  // i2c_master_get_bus_handle() fills bus and returns ESP_OK if the port was
  // previously initialized by another driver; returns an error if not.
  i2c_master_bus_handle_t bus = nullptr;
  esp_err_t probe = i2c_master_get_bus_handle(config_.i2c_port, &bus);
  if (probe == ESP_OK) {
    ESP_LOGI(kTag, "Reusing existing I2C bus on port %d", config_.i2c_port);
  } else {
    // No bus on this port yet — create and own it.
    i2c_master_bus_config_t bus_cfg          = {};
    bus_cfg.i2c_port                         = config_.i2c_port;
    bus_cfg.sda_io_num                       = config_.sda_pin;
    bus_cfg.scl_io_num                       = config_.scl_pin;
    bus_cfg.clk_source                       = I2C_CLK_SRC_DEFAULT;
    bus_cfg.glitch_ignore_cnt                = 7;
    bus_cfg.flags.enable_internal_pullup     = true;

    esp_err_t ret = i2c_new_master_bus(&bus_cfg, &bus);
    if (ret != ESP_OK) {
      ESP_LOGE(kTag, "Failed to create I2C bus: %s", esp_err_to_name(ret));
      return false;
    }
    owned_bus_handle_ = bus;
    ESP_LOGI(kTag, "Created I2C bus on port %d", config_.i2c_port);
  }

  // Register the device on the bus.
  i2c_device_config_t dev_cfg = {};
  dev_cfg.dev_addr_length = I2C_ADDR_BIT_LEN_7;
  dev_cfg.device_address  = config_.i2c_address;
  dev_cfg.scl_speed_hz    = config_.i2c_speed_hz;

  esp_err_t ret = i2c_master_bus_add_device(bus, &dev_cfg, &i2c_handle_);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to add I2C device: %s", esp_err_to_name(ret));
    i2c_handle_ = nullptr;
    if (owned_bus_handle_ != nullptr) {
      i2c_del_master_bus(owned_bus_handle_);
      owned_bus_handle_ = nullptr;
    }
    return false;
  }

  // Soft-reset to clear any leftover register state.
  if (!SoftReset()) { Deinit(); return false; }

  // Wait for sensor hardware and calibration coefficients to be ready.
  esp_err_t wait = WaitSensorReady();
  if (wait != ESP_OK) { Deinit(); return false; }

  // Read calibration coefficients from OTP.
  esp_err_t coef = ReadCalibrationCoefficients();
  if (coef != ESP_OK) {
    ESP_LOGE(kTag, "Failed to read calibration coefficients: %s",
             esp_err_to_name(coef));
    Deinit();
    return false;
  }

  // Apply all settings from Config.
  if (!ApplyConfig()) { Deinit(); return false; }

  ESP_LOGI(kTag, "Initialized. P-OSR=%d P-rate=%d T-OSR=%d T-rate=%d mode=%d",
           static_cast<int>(config_.pressure_osr),
           static_cast<int>(config_.pressure_rate),
           static_cast<int>(config_.temperature_osr),
           static_cast<int>(config_.temperature_rate),
           static_cast<int>(config_.measurement_mode));
  return true;
}

bool Spl06003::Deinit() {
  if (i2c_handle_ == nullptr) {
    return true;  // Already deinitialized; nothing to do.
  }

  bool ok = true;

  esp_err_t ret = i2c_master_bus_rm_device(i2c_handle_);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to remove I2C device: %s", esp_err_to_name(ret));
    ok = false;
  }
  i2c_handle_ = nullptr;

  if (owned_bus_handle_ != nullptr) {
    ret = i2c_del_master_bus(owned_bus_handle_);
    if (ret != ESP_OK) {
      ESP_LOGE(kTag, "Failed to delete I2C bus: %s", esp_err_to_name(ret));
      ok = false;
    }
    owned_bus_handle_ = nullptr;
  }

  ESP_LOGI(kTag, "Deinitialized");
  return ok;
}

// ---------------------------------------------------------------------------
// Sensor control
// ---------------------------------------------------------------------------

bool Spl06003::SoftReset() {
  // Writing kResetSoftReset triggers a full reset; the device is ready again
  // after ~40 ms (WaitSensorReady() should follow).
  esp_err_t ret = WriteRegister(kRegReset, kResetSoftReset);
  if (ret != ESP_OK) return false;
  vTaskDelay(pdMS_TO_TICKS(40));
  return true;
}

bool Spl06003::SetPressureConfig(PressureOversamplingRate osr,
                                  PressureMeasurementRate rate) {
  uint8_t val = (static_cast<uint8_t>(rate) << 4) |
                 static_cast<uint8_t>(osr);
  esp_err_t ret = WriteRegister(kRegPrsCfg, val);
  if (ret == ESP_OK) {
    prs_osr_ = static_cast<uint8_t>(osr);
    return true;
  }
  return false;
}

bool Spl06003::SetTemperatureConfig(TemperatureOversamplingRate osr,
                                     TemperatureMeasurementRate rate,
                                     TemperatureSource source) {
  uint8_t val = (static_cast<uint8_t>(source) << 7) |
                (static_cast<uint8_t>(rate) << 4)   |
                 static_cast<uint8_t>(osr);
  esp_err_t ret = WriteRegister(kRegTmpCfg, val);
  if (ret == ESP_OK) {
    tmp_osr_ = static_cast<uint8_t>(osr);
    return true;
  }
  return false;
}

bool Spl06003::SetMeasurementMode(MeasurementMode mode) {
  uint8_t current = 0;
  esp_err_t ret = ReadRegister(kRegMeasCfg, &current);
  if (ret != ESP_OK) return false;
  current = (current & 0xF8) | static_cast<uint8_t>(mode);
  return WriteRegister(kRegMeasCfg, current) == ESP_OK;
}

bool Spl06003::SetResultBitShift(bool enable_pressure_shift,
                                  bool enable_temperature_shift) {
  uint8_t cfg = 0;
  esp_err_t ret = ReadRegister(kRegCfgReg, &cfg);
  if (ret != ESP_OK) return false;

  if (enable_pressure_shift)    { cfg |= kCfgPrsShift; } else { cfg &= ~kCfgPrsShift; }
  if (enable_temperature_shift) { cfg |= kCfgTmpShift; } else { cfg &= ~kCfgTmpShift; }
  return WriteRegister(kRegCfgReg, cfg) == ESP_OK;
}

bool Spl06003::SetFifoEnabled(bool enabled) {
  uint8_t cfg = 0;
  esp_err_t ret = ReadRegister(kRegCfgReg, &cfg);
  if (ret != ESP_OK) return false;
  if (enabled) { cfg |= kCfgFifoEn; } else { cfg &= ~kCfgFifoEn; }
  return WriteRegister(kRegCfgReg, cfg) == ESP_OK;
}

bool Spl06003::SetInterruptConfig(bool active_high, bool fifo_full_int,
                                   bool pressure_rdy_int, bool temp_rdy_int) {
  uint8_t cfg = 0;
  esp_err_t ret = ReadRegister(kRegCfgReg, &cfg);
  if (ret != ESP_OK) return false;

  cfg &= ~(kCfgIntHlActive | kCfgIntFifo | kCfgIntTmp | kCfgIntPrs);
  if (active_high)      cfg |= kCfgIntHlActive;
  if (fifo_full_int)    cfg |= kCfgIntFifo;
  if (pressure_rdy_int) cfg |= kCfgIntPrs;
  if (temp_rdy_int)     cfg |= kCfgIntTmp;
  return WriteRegister(kRegCfgReg, cfg) == ESP_OK;
}

bool Spl06003::FlushFifo() {
  return WriteRegister(kRegReset, kResetFifoFlush) == ESP_OK;
}

bool Spl06003::Update() {
  uint8_t meas_cfg = 0;
  esp_err_t ret = ReadRegister(kRegMeasCfg, &meas_cfg);
  if (ret != ESP_OK) return false;

  if (!(meas_cfg & kMeasCfgPrsRdy) || !(meas_cfg & kMeasCfgTmpRdy)) {
    // Data not yet ready — not an error.
    return true;
  }

  // Read pressure raw (3 bytes from 0x00).
  uint8_t prs_buf[3] = {};
  ret = ReadRegisters(kRegPsrB2, prs_buf, 3);
  if (ret != ESP_OK) return false;

  // Read temperature raw (3 bytes from 0x03).
  uint8_t tmp_buf[3] = {};
  ret = ReadRegisters(kRegTmpB2, tmp_buf, 3);
  if (ret != ESP_OK) return false;

  uint32_t prs_raw_u = (static_cast<uint32_t>(prs_buf[0]) << 16) |
                       (static_cast<uint32_t>(prs_buf[1]) << 8)  |
                        static_cast<uint32_t>(prs_buf[2]);
  uint32_t tmp_raw_u = (static_cast<uint32_t>(tmp_buf[0]) << 16) |
                       (static_cast<uint32_t>(tmp_buf[1]) << 8)  |
                        static_cast<uint32_t>(tmp_buf[2]);

  int32_t prs_raw = TwosComplement24(prs_raw_u);
  int32_t tmp_raw = TwosComplement24(tmp_raw_u);

  float kp = static_cast<float>(GetScaleFactor(prs_osr_));
  float kt = static_cast<float>(GetScaleFactor(tmp_osr_));

  float traw_sc = static_cast<float>(tmp_raw) / kt;
  float praw_sc = static_cast<float>(prs_raw) / kp;

  // Compensated temperature (°C) — SPL06 datasheet Equation 1.
  temperature_c_ = static_cast<float>(c0_) * 0.5f +
                   static_cast<float>(c1_) * traw_sc;

  // Compensated pressure (Pa) — SPL06 datasheet Equation 2.
  pressure_pa_ =
      static_cast<float>(c00_) +
      praw_sc * (static_cast<float>(c10_) +
                 praw_sc * (static_cast<float>(c20_) +
                            praw_sc * static_cast<float>(c30_))) +
      traw_sc * static_cast<float>(c01_) +
      traw_sc * praw_sc * (static_cast<float>(c11_) +
                           praw_sc * static_cast<float>(c21_));

  return true;
}

float Spl06003::GetAltitudeMeters(float sea_level_pa) const {
  return 44330.0f * (1.0f - powf(pressure_pa_ / sea_level_pa, 0.1903f));
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

bool Spl06003::ApplyConfig() {
  if (!SetPressureConfig(config_.pressure_osr, config_.pressure_rate)) return false;
  if (!SetTemperatureConfig(config_.temperature_osr, config_.temperature_rate,
                             config_.temperature_source)) return false;
  if (!SetResultBitShift(config_.pressure_result_shift,
                          config_.temperature_result_shift)) return false;
  return SetMeasurementMode(config_.measurement_mode);
}

esp_err_t Spl06003::WaitSensorReady() {
  const uint32_t kTimeoutMs = 500;
  const uint32_t kPollMs    = 10;
  uint32_t elapsed = 0;

  while (elapsed < kTimeoutMs) {
    uint8_t status = 0;
    esp_err_t ret = ReadRegister(kRegMeasCfg, &status);
    if (ret != ESP_OK) return ret;

    if ((status & kMeasCfgSensorRdy) && (status & kMeasCfgCoefRdy)) {
      return ESP_OK;
    }
    vTaskDelay(pdMS_TO_TICKS(kPollMs));
    elapsed += kPollMs;
  }

  ESP_LOGE(kTag, "Sensor not ready within %lu ms timeout", (unsigned long)kTimeoutMs);
  return ESP_ERR_TIMEOUT;
}

esp_err_t Spl06003::ReadCalibrationCoefficients() {
  // 18 bytes of OTP coefficient data starting at kRegCoefStart (0x10).
  uint8_t buf[18] = {};
  esp_err_t ret = ReadRegisters(kRegCoefStart, buf, sizeof(buf));
  if (ret != ESP_OK) return ret;

  // Parse per SPL06-003 datasheet Table 9.

  // c0: 12-bit signed. [11:4]=buf[0], [3:0]=buf[1][7:4].
  c0_ = static_cast<int32_t>((static_cast<uint32_t>(buf[0]) << 4) |
                              (static_cast<uint32_t>(buf[1]) >> 4));
  if (c0_ & 0x800) c0_ |= static_cast<int32_t>(0xFFFFF000);

  // c1: 12-bit signed. [11:8]=buf[1][3:0], [7:0]=buf[2].
  c1_ = static_cast<int32_t>(((static_cast<uint32_t>(buf[1]) & 0x0F) << 8) |
                               static_cast<uint32_t>(buf[2]));
  if (c1_ & 0x800) c1_ |= static_cast<int32_t>(0xFFFFF000);

  // c00: 20-bit signed.
  c00_ = static_cast<int32_t>((static_cast<uint32_t>(buf[3]) << 12) |
                               (static_cast<uint32_t>(buf[4]) << 4)  |
                               (static_cast<uint32_t>(buf[5]) >> 4));
  if (c00_ & 0x80000) c00_ |= static_cast<int32_t>(0xFFF00000);

  // c10: 20-bit signed.
  c10_ = static_cast<int32_t>(((static_cast<uint32_t>(buf[5]) & 0x0F) << 16) |
                                (static_cast<uint32_t>(buf[6]) << 8)          |
                                 static_cast<uint32_t>(buf[7]));
  if (c10_ & 0x80000) c10_ |= static_cast<int32_t>(0xFFF00000);

  // c01, c11, c20, c21, c30: 16-bit signed.
  c01_ = static_cast<int16_t>((static_cast<uint16_t>(buf[8])  << 8) | buf[9]);
  c11_ = static_cast<int16_t>((static_cast<uint16_t>(buf[10]) << 8) | buf[11]);
  c20_ = static_cast<int16_t>((static_cast<uint16_t>(buf[12]) << 8) | buf[13]);
  c21_ = static_cast<int16_t>((static_cast<uint16_t>(buf[14]) << 8) | buf[15]);
  c30_ = static_cast<int16_t>((static_cast<uint16_t>(buf[16]) << 8) | buf[17]);

  ESP_LOGD(kTag,
           "Coef c0=%ld c1=%ld c00=%ld c10=%ld c01=%ld "
           "c11=%ld c20=%ld c21=%ld c30=%ld",
           (long)c0_, (long)c1_, (long)c00_, (long)c10_,
           (long)c01_, (long)c11_, (long)c20_, (long)c21_, (long)c30_);
  return ESP_OK;
}

int32_t Spl06003::TwosComplement24(uint32_t raw) {
  if (raw & 0x800000) {
    return static_cast<int32_t>(raw | 0xFF000000U);
  }
  return static_cast<int32_t>(raw);
}

int32_t Spl06003::GetScaleFactor(uint8_t osr) {
  if (osr >= 8) osr = 7;
  return kScaleFactors[osr];
}

esp_err_t Spl06003::WriteRegister(Register reg, uint8_t value) {
  uint8_t buf[2] = {static_cast<uint8_t>(reg), value};
  return i2c_master_transmit(i2c_handle_, buf, sizeof(buf), -1);
}

esp_err_t Spl06003::ReadRegister(Register reg, uint8_t* value) {
  uint8_t reg_addr = static_cast<uint8_t>(reg);
  return i2c_master_transmit_receive(i2c_handle_, &reg_addr, 1, value, 1, -1);
}

esp_err_t Spl06003::ReadRegisters(Register start_reg, uint8_t* buf,
                                   size_t len) {
  uint8_t reg_addr = static_cast<uint8_t>(start_reg);
  return i2c_master_transmit_receive(i2c_handle_, &reg_addr, 1, buf, len, -1);
}
