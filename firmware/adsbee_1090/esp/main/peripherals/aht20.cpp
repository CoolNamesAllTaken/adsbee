#include "aht20.hh"

#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

static const char* kTag = "AHT20";

// ---------------------------------------------------------------------------
// Constructor / Destructor
// ---------------------------------------------------------------------------

Aht20::Aht20(const Config& config)
    : config_(config),
      i2c_handle_(nullptr),
      owned_bus_handle_(nullptr),
      temperature_c_(0.0f),
      humidity_rh_(0.0f),
      calibrated_(false),
      measurement_pending_(false) {}

Aht20::~Aht20() {
  if (i2c_handle_ != nullptr) {
    Deinit();
  }
}

// ---------------------------------------------------------------------------
// Lifecycle
// ---------------------------------------------------------------------------

bool Aht20::Init() {
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

  // The AHT20 needs 40 ms after power-on before the first command.
  vTaskDelay(pdMS_TO_TICKS(kStartupTimeMs));

  if (!EnsureCalibrated()) {
    ESP_LOGE(kTag, "Calibration check failed");
    Deinit();
    return false;
  }

  ESP_LOGI(kTag, "Initialized successfully");
  return true;
}

bool Aht20::Deinit() {
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
  calibrated_          = false;
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

bool Aht20::SoftReset() {
  uint8_t cmd = kCmdSoftReset;
  esp_err_t ret = i2c_master_transmit(i2c_handle_, &cmd, 1, -1);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Soft reset command failed: %s", esp_err_to_name(ret));
    return false;
  }
  vTaskDelay(pdMS_TO_TICKS(kSoftResetTimeMs));
  calibrated_ = false;
  return EnsureCalibrated();
}

bool Aht20::TriggerMeasurement() {
  uint8_t cmd[3] = {kCmdTriggerMeasure, kMeasureParam1, kMeasureParam2};
  esp_err_t ret = i2c_master_transmit(i2c_handle_, cmd, sizeof(cmd), -1);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Trigger measurement failed: %s", esp_err_to_name(ret));
    return false;
  }
  return true;
}

bool Aht20::IsBusy(bool* busy) {
  uint8_t status = 0;
  esp_err_t ret = ReadStatus(&status);
  if (ret != ESP_OK) return false;
  *busy = (status & kStatusBusy) != 0;
  return true;
}

bool Aht20::ReadMeasurement() {
  // Read 6 bytes: 1 status byte + 5 data bytes.
  uint8_t buf[6] = {};
  esp_err_t ret = i2c_master_receive(i2c_handle_, buf, sizeof(buf), -1);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Read measurement failed: %s", esp_err_to_name(ret));
    return false;
  }

  if (buf[0] & kStatusBusy) {
    ESP_LOGW(kTag, "Sensor still busy — data not yet valid");
    return false;
  }

  // Humidity: bits[19:0] of bytes 1–3 (upper 20 bits of the combined field).
  uint32_t hum_raw = (static_cast<uint32_t>(buf[1]) << 12) |
                     (static_cast<uint32_t>(buf[2]) << 4)  |
                     (static_cast<uint32_t>(buf[3]) >> 4);

  // Temperature: lower nibble of byte 3 + full bytes 4 and 5.
  uint32_t temp_raw = ((static_cast<uint32_t>(buf[3]) & 0x0F) << 16) |
                       (static_cast<uint32_t>(buf[4]) << 8)            |
                        static_cast<uint32_t>(buf[5]);

  humidity_rh_   = (static_cast<float>(hum_raw)  / 1048576.0f) * 100.0f;
  temperature_c_ = (static_cast<float>(temp_raw) / 1048576.0f) * 200.0f - 50.0f;

  return true;
}

bool Aht20::Update() {
  if (!measurement_pending_) {
    if (!TriggerMeasurement()) return false;
    measurement_pending_ = true;
    return true;
  }

  bool busy = false;
  if (!IsBusy(&busy)) return false;

  if (busy) {
    return true;
  }

  if (!ReadMeasurement()) return false;

  if (!TriggerMeasurement()) {
    measurement_pending_ = false;
    return false;
  }

  return true;
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

bool Aht20::EnsureCalibrated() {
  uint8_t status = 0;
  esp_err_t ret = ReadStatus(&status);
  if (ret != ESP_OK) return false;

  if (status & kStatusCalibrated) {
    calibrated_ = true;
    return true;
  }

  // Send initialisation command to trigger internal calibration.
  uint8_t cmd[3] = {kCmdInitialize, kInitParam1, kInitParam2};
  ret = i2c_master_transmit(i2c_handle_, cmd, sizeof(cmd), -1);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Initialise command failed: %s", esp_err_to_name(ret));
    return false;
  }
  vTaskDelay(pdMS_TO_TICKS(10));

  ret = ReadStatus(&status);
  if (ret != ESP_OK) return false;

  if (!(status & kStatusCalibrated)) {
    ESP_LOGE(kTag, "Sensor not calibrated after init command");
    return false;
  }

  calibrated_ = true;
  return true;
}

esp_err_t Aht20::ReadStatus(uint8_t* status) {
  uint8_t cmd = kCmdGetStatus;
  return i2c_master_transmit_receive(i2c_handle_, &cmd, 1, status, 1, -1);
}
