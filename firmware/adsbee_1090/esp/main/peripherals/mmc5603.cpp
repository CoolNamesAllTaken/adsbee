#include "mmc5603.hh"

#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

static const char* kTag = "MMC5603";

// ---------------------------------------------------------------------------
// Constructor / Destructor
// ---------------------------------------------------------------------------

Mmc5603::Mmc5603(const Config& config)
    : config_(config),
      i2c_handle_(nullptr),
      owned_bus_handle_(nullptr),
      mag_x_gauss_(0.0f),
      mag_y_gauss_(0.0f),
      mag_z_gauss_(0.0f),
      temperature_c_(0.0f),
      measurement_pending_(false) {}

Mmc5603::~Mmc5603() {
  if (i2c_handle_ != nullptr) {
    Deinit();
  }
}

// ---------------------------------------------------------------------------
// Lifecycle
// ---------------------------------------------------------------------------

bool Mmc5603::Init() {
  if (i2c_handle_ != nullptr) {
    ESP_LOGW(kTag, "Already initialized — call Deinit() first");
    return false;
  }

  // Try to claim an already-initialized bus on the configured port.
  i2c_master_bus_handle_t bus = nullptr;
  esp_err_t probe = i2c_master_get_bus_handle(config_.i2c_port, &bus);
  if (probe == ESP_OK) {
    ESP_LOGI(kTag, "Reusing existing I2C bus on port %d", config_.i2c_port);
  } else {
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

  i2c_device_config_t dev_cfg = {};
  dev_cfg.dev_addr_length = I2C_ADDR_BIT_LEN_7;
  dev_cfg.device_address  = kI2cAddress;
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

  if (!Configure()) {
    Deinit();
    return false;
  }
  return true;
}

bool Mmc5603::Deinit() {
  if (i2c_handle_ == nullptr) {
    return true;
  }

  bool ok = true;

  esp_err_t ret = i2c_master_bus_rm_device(i2c_handle_);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to remove I2C device: %s", esp_err_to_name(ret));
    ok = false;
  }
  i2c_handle_          = nullptr;
  measurement_pending_ = false;

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

bool Mmc5603::SoftReset() {
  // SW_RST is self-clearing; the part re-reads OTP and takes ~20 ms.
  esp_err_t ret = WriteReg(kRegCtrl1, kCtrl1SwReset);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Soft reset command failed: %s", esp_err_to_name(ret));
    return false;
  }
  measurement_pending_ = false;
  vTaskDelay(pdMS_TO_TICKS(kStartupTimeMs));
  return Configure();
}

bool Mmc5603::TriggerMeasurement() {
  uint8_t ctrl0 = kCtrl0TakeMeasM;
  if (config_.auto_set_reset) {
    ctrl0 |= kCtrl0AutoSrEn;
  }
  esp_err_t ret = WriteReg(kRegCtrl0, ctrl0);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Trigger measurement failed: %s", esp_err_to_name(ret));
    return false;
  }
  measurement_pending_ = true;
  return true;
}

bool Mmc5603::IsMeasurementReady(bool* ready) {
  uint8_t status = 0;
  esp_err_t ret  = ReadRegs(kRegStatus, &status, 1);
  if (ret != ESP_OK) return false;
  *ready = (status & kStatusMeasMDone) != 0;
  return true;
}

bool Mmc5603::ReadMeasurement() {
  // Read 9 consecutive registers: Xout0..Zout2 (0x00–0x08).
  uint8_t buf[9] = {};
  esp_err_t ret  = ReadRegs(kRegXout0, buf, sizeof(buf));
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Read measurement failed: %s", esp_err_to_name(ret));
    return false;
  }

  uint32_t x_raw = (static_cast<uint32_t>(buf[0]) << 12) |
                   (static_cast<uint32_t>(buf[1]) <<  4) |
                   (static_cast<uint32_t>(buf[6]) >>  4);
  uint32_t y_raw = (static_cast<uint32_t>(buf[2]) << 12) |
                   (static_cast<uint32_t>(buf[3]) <<  4) |
                   (static_cast<uint32_t>(buf[7]) >>  4);
  uint32_t z_raw = (static_cast<uint32_t>(buf[4]) << 12) |
                   (static_cast<uint32_t>(buf[5]) <<  4) |
                   (static_cast<uint32_t>(buf[8]) >>  4);

  mag_x_gauss_ = (static_cast<float>(x_raw) - kNullFieldCounts) / kCountsPerGauss;
  mag_y_gauss_ = (static_cast<float>(y_raw) - kNullFieldCounts) / kCountsPerGauss;
  mag_z_gauss_ = (static_cast<float>(z_raw) - kNullFieldCounts) / kCountsPerGauss;

  uint8_t temp_raw = 0;
  ret = ReadRegs(kRegTemp, &temp_raw, 1);
  if (ret == ESP_OK) {
    temperature_c_ = kTempOffset + static_cast<float>(temp_raw) * kTempScale;
  }

  return true;
}

bool Mmc5603::Update() {
  if (!measurement_pending_) {
    return TriggerMeasurement();
  }

  bool ready = false;
  if (!IsMeasurementReady(&ready)) return false;

  if (!ready) {
    return true;
  }

  if (!ReadMeasurement()) {
    measurement_pending_ = false;
    return false;
  }

  if (!TriggerMeasurement()) {
    measurement_pending_ = false;
    return false;
  }

  return true;
}

bool Mmc5603::Configure() {
  // The MMC5603 needs up to 20 ms after power-on or soft-reset.
  vTaskDelay(pdMS_TO_TICKS(kStartupTimeMs));

  uint8_t chip_id = 0;
  esp_err_t ret = ReadRegs(kRegProdId, &chip_id, 1);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to read product ID: %s", esp_err_to_name(ret));
    return false;
  }
  // Some early production units report 0x00; accept both for robustness.
  if (chip_id != kExpectedChipId && chip_id != 0x00) {
    ESP_LOGE(kTag, "Unexpected product ID: 0x%02X (expected 0x%02X or 0x00)",
             chip_id, kExpectedChipId);
    return false;
  }
  ESP_LOGI(kTag, "Product ID: 0x%02X", chip_id);

  ret = WriteReg(kRegCtrl1, config_.bandwidth & 0x03);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to set bandwidth: %s", esp_err_to_name(ret));
    return false;
  }

  ret = PerformSet();
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Initial SET failed: %s", esp_err_to_name(ret));
    return false;
  }

  if (!TriggerMeasurement()) {
    ESP_LOGE(kTag, "Failed to trigger initial measurement");
    return false;
  }

  ESP_LOGI(kTag, "Configured (BW=%u, AutoSR=%s)",
           config_.bandwidth & 0x03,
           config_.auto_set_reset ? "on" : "off");
  return true;
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

esp_err_t Mmc5603::WriteReg(uint8_t reg, uint8_t value) {
  uint8_t buf[2] = {reg, value};
  return i2c_master_transmit(i2c_handle_, buf, sizeof(buf), -1);
}

esp_err_t Mmc5603::ReadRegs(uint8_t start_reg, uint8_t* buf, size_t len) {
  return i2c_master_transmit_receive(i2c_handle_, &start_reg, 1, buf, len, -1);
}

esp_err_t Mmc5603::PerformSet() {
  esp_err_t ret = WriteReg(kRegCtrl0, kCtrl0DoSet);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "SET command failed: %s", esp_err_to_name(ret));
    return ret;
  }
  vTaskDelay(pdMS_TO_TICKS(kSetResetTimeMs));
  return ESP_OK;
}
