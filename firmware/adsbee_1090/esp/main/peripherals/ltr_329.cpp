#include "ltr_329.hh"

#include <cmath>
#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

static const char* kTag = "LTR329";

// Integration time in ms indexed by IntegrationTime enum value.
static constexpr float kIntegrationTimeMs[] = {
    100.0f,  // kTime100ms (0)
    50.0f,   // kTime50ms  (1)
    200.0f,  // kTime200ms (2)
    400.0f,  // kTime400ms (3)
    150.0f,  // kTime150ms (4)
    250.0f,  // kTime250ms (5)
    300.0f,  // kTime300ms (6)
    350.0f,  // kTime350ms (7)
};

// Gain multipliers indexed by Gain enum value.
static constexpr float kGainMultipliers[] = {
    1.0f,   // kGain1x  (0)
    2.0f,   // kGain2x  (1)
    4.0f,   // kGain4x  (2)
    8.0f,   // kGain8x  (3)
    1.0f,   // reserved (4)
    1.0f,   // reserved (5)
    48.0f,  // kGain48x (6)
    96.0f,  // kGain96x (7)
};

// ---------------------------------------------------------------------------
// Constructor / Destructor
// ---------------------------------------------------------------------------

Ltr329::Ltr329(const Config& config)
    : config_(config),
      i2c_handle_(nullptr),
      owned_bus_handle_(nullptr),
      current_gain_(config.gain),
      current_integration_time_(config.integration_time),
      ch0_raw_(0),
      ch1_raw_(0),
      lux_(0.0f),
      data_valid_(false) {}

Ltr329::~Ltr329() {
  if (i2c_handle_ != nullptr) {
    Deinit();
  }
}

// ---------------------------------------------------------------------------
// Lifecycle
// ---------------------------------------------------------------------------

bool Ltr329::Init() {
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

  // Verify Part ID.
  uint8_t part_id = 0;
  ret = ReadRegister(kRegPartId, &part_id);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to read Part ID: %s", esp_err_to_name(ret));
    Deinit();
    return false;
  }
  if ((part_id & kPartIdMask) != kExpectedPartId) {
    ESP_LOGE(kTag, "Unexpected Part ID: 0x%02X", part_id);
    Deinit();
    return false;
  }

  // Verify Manufacturer ID.
  uint8_t manuf_id = 0;
  ret = ReadRegister(kRegManufacId, &manuf_id);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to read Manufacturer ID: %s", esp_err_to_name(ret));
    Deinit();
    return false;
  }
  if (manuf_id != kManufacturerId) {
    ESP_LOGE(kTag, "Unexpected Manufacturer ID: 0x%02X", manuf_id);
    Deinit();
    return false;
  }

  // Soft-reset to put the device into a known state.
  if (!SoftReset()) {
    Deinit();
    return false;
  }

  // Apply configuration from Config struct.
  if (!SetGain(config_.gain)) { Deinit(); return false; }
  if (!SetMeasurementConfig(config_.integration_time, config_.measurement_rate)) { Deinit(); return false; }
  if (!SetActiveMode()) { Deinit(); return false; }

  ESP_LOGI(kTag, "Initialized. Part ID: 0x%02X, gain=%d, t_int=%d, rate=%d",
           part_id,
           static_cast<int>(config_.gain),
           static_cast<int>(config_.integration_time),
           static_cast<int>(config_.measurement_rate));
  return true;
}

bool Ltr329::Deinit() {
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
  data_valid_  = false;

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

bool Ltr329::SoftReset() {
  esp_err_t ret = WriteRegister(kRegAlsContr, kContrSwReset);
  if (ret != ESP_OK) return false;
  vTaskDelay(pdMS_TO_TICKS(10));  // 10ms reset time per datasheet.
  return true;
}

bool Ltr329::SetGain(Gain gain) {
  uint8_t contr = 0;
  esp_err_t ret = ReadRegister(kRegAlsContr, &contr);
  if (ret != ESP_OK) return false;

  contr &= ~kContrGainMask;
  contr |= (static_cast<uint8_t>(gain) << kContrGainShift) & kContrGainMask;

  ret = WriteRegister(kRegAlsContr, contr);
  if (ret == ESP_OK) {
    current_gain_ = gain;
    return true;
  }
  return false;
}

bool Ltr329::SetMeasurementConfig(IntegrationTime integration_time,
                                   MeasurementRate measurement_rate) {
  uint8_t val = (static_cast<uint8_t>(integration_time) << 3) |
                 static_cast<uint8_t>(measurement_rate);
  esp_err_t ret = WriteRegister(kRegAlsMeasRate, val);
  if (ret == ESP_OK) {
    current_integration_time_ = integration_time;
    return true;
  }
  return false;
}

bool Ltr329::SetActiveMode() {
  uint8_t contr = 0;
  esp_err_t ret = ReadRegister(kRegAlsContr, &contr);
  if (ret != ESP_OK) return false;
  contr |= kContrAlsMode;
  return WriteRegister(kRegAlsContr, contr) == ESP_OK;
}

bool Ltr329::SetStandbyMode() {
  uint8_t contr = 0;
  esp_err_t ret = ReadRegister(kRegAlsContr, &contr);
  if (ret != ESP_OK) return false;
  contr &= ~kContrAlsMode;
  return WriteRegister(kRegAlsContr, contr) == ESP_OK;
}

bool Ltr329::Update() {
  // Check status for new data flag.
  uint8_t status = 0;
  esp_err_t ret = ReadRegister(kRegAlsStatus, &status);
  if (ret != ESP_OK) return false;

  data_valid_ = false;

  if (!(status & kStatusDataNew)) {
    // No new data available yet — not an error.
    return true;
  }

  // Read 4 bytes: CH1_L, CH1_H, CH0_L, CH0_H (burst from 0x88).
  uint8_t buf[4] = {};
  ret = ReadRegisters(kRegAlsDataCh1L, buf, 4);
  if (ret != ESP_OK) return false;

  ch1_raw_ = static_cast<uint16_t>(buf[0]) |
             (static_cast<uint16_t>(buf[1]) << 8);
  ch0_raw_ = static_cast<uint16_t>(buf[2]) |
             (static_cast<uint16_t>(buf[3]) << 8);

  lux_       = ComputeLux(ch0_raw_, ch1_raw_);
  data_valid_ = true;
  UpdateAmbientLevel();
  return true;
}

void Ltr329::UpdateAmbientLevel() {
  // Normalize lux -> 0..1 on a log scale (floor lux so logf() is finite).
  float l     = (lux_ < 1.0f) ? 1.0f : lux_;
  float level = (logf(l) - logf(config_.lux_min)) /
                (logf(config_.lux_max) - logf(config_.lux_min));
  if (level < 0.0f) level = 0.0f;
  if (level > 1.0f) level = 1.0f;

  // Seed on the first valid reading so the level doesn't ramp up from 0 on
  // boot; EMA-smooth thereafter to avoid flicker from noisy readings.
  if (!ambient_level_seeded_) {
    ambient_level_        = level;
    ambient_level_seeded_ = true;
  } else {
    ambient_level_ += config_.ema_alpha * (level - ambient_level_);
  }
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

float Ltr329::ComputeLux(uint16_t ch0, uint16_t ch1) {
  if (ch0 == 0 && ch1 == 0) return 0.0f;

  float ch0f  = static_cast<float>(ch0);
  float ch1f  = static_cast<float>(ch1);
  float ratio = ch1f / (ch0f + ch1f);

  float gain  = kGainMultipliers[static_cast<uint8_t>(current_gain_)];
  float t_int = kIntegrationTimeMs[static_cast<uint8_t>(current_integration_time_)];

  // Normalise counts to gain=1x, t_int=100ms baseline.
  float als_ch0 = ch0f / (gain * t_int / 100.0f);
  float als_ch1 = ch1f / (gain * t_int / 100.0f);

  float lux = 0.0f;
  if (ratio < 0.45f) {
    lux = 1.7743f * als_ch0 + 1.1059f * als_ch1;
  } else if (ratio < 0.64f) {
    lux = 4.2785f * als_ch0 - 1.9548f * als_ch1;
  } else if (ratio < 0.85f) {
    lux = 0.5926f * als_ch0 + 0.1185f * als_ch1;
  } else {
    lux = 0.0f;  // Sensor saturated / invalid.
  }

  return (lux < 0.0f) ? 0.0f : lux;
}

esp_err_t Ltr329::WriteRegister(Register reg, uint8_t value) {
  uint8_t buf[2] = {static_cast<uint8_t>(reg), value};
  return i2c_master_transmit(i2c_handle_, buf, sizeof(buf), -1);
}

esp_err_t Ltr329::ReadRegister(Register reg, uint8_t* value) {
  uint8_t reg_addr = static_cast<uint8_t>(reg);
  return i2c_master_transmit_receive(i2c_handle_, &reg_addr, 1, value, 1, -1);
}

esp_err_t Ltr329::ReadRegisters(Register start_reg, uint8_t* buf, size_t len) {
  uint8_t reg_addr = static_cast<uint8_t>(start_reg);
  return i2c_master_transmit_receive(i2c_handle_, &reg_addr, 1, buf, len, -1);
}
