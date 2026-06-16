#include "bq27427.hh"

#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

static const char* kTag = "BQ27427";

// Expected value returned by the DEVICE_TYPE subcommand (0x0001).
static constexpr uint16_t kExpectedDeviceType = 0x0427;

// ---------------------------------------------------------------------------
// Constructor / Destructor
// ---------------------------------------------------------------------------

Bq27427::Bq27427(const Config& config)
    : config_(config),
      i2c_handle_(nullptr),
      owned_bus_handle_(nullptr),
      last_update_us_(0),
      average_power_mw_(0),
      state_of_charge_pct_(0),
      flags_(0),
      data_valid_(false) {}

Bq27427::~Bq27427() {
  if (i2c_handle_ != nullptr) {
    Deinit();
  }
}

// ---------------------------------------------------------------------------
// Lifecycle
// ---------------------------------------------------------------------------

bool Bq27427::Init() {
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

  // Allow time for POR / INITIALIZATION to complete before communicating.
  vTaskDelay(pdMS_TO_TICKS(kInitWaitMs));

  // Verify device identity via the DEVICE_TYPE subcommand.
  ret = WriteSubCmd(kSubCmdDeviceType);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to write DEVICE_TYPE subcommand: %s",
             esp_err_to_name(ret));
    Deinit();
    return false;
  }
  uint16_t device_type = 0;
  ret = ReadWord(kCmdControl, &device_type);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to read DEVICE_TYPE: %s", esp_err_to_name(ret));
    Deinit();
    return false;
  }
  if (device_type != kExpectedDeviceType) {
    ESP_LOGE(kTag, "Unexpected device type: 0x%04X (expected 0x%04X)",
             device_type, kExpectedDeviceType);
    Deinit();
    return false;
  }
  ESP_LOGI(kTag, "Device type confirmed: 0x%04X", device_type);

  // Signal battery insertion via software subcommand if requested.
  // Required when OpConfig [BIE] = 0 (the default): the gauge relies on the
  // host — not the BIN pin — to detect a battery.
  if (config_.send_bat_insert) {
    ret = WriteSubCmd(kSubCmdBatInsert);
    if (ret != ESP_OK) {
      ESP_LOGE(kTag, "Failed to send BAT_INSERT: %s", esp_err_to_name(ret));
      Deinit();
      return false;
    }
    ESP_LOGI(kTag, "BAT_INSERT subcommand sent");
  }

  // Prime the cache with a first read.
  if (!Update()) {
    ESP_LOGE(kTag, "Initial Update() failed");
    Deinit();
    return false;
  }

  ESP_LOGI(kTag, "Initialized — SOC:%u%% AvgPwr:%dmW Flags:0x%04X",
           state_of_charge_pct_, average_power_mw_, flags_);
  return true;
}

bool Bq27427::Deinit() {
  if (i2c_handle_ == nullptr) {
    return true;
  }

  bool ok = true;

  esp_err_t ret = i2c_master_bus_rm_device(i2c_handle_);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to remove I2C device: %s", esp_err_to_name(ret));
    ok = false;
  }
  i2c_handle_ = nullptr;
  data_valid_ = false;

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
// Sensor polling
// ---------------------------------------------------------------------------

bool Bq27427::Update() {
  // Enforce the TRM's ≤2 standard-command-reads/second limit internally.
  const int64_t now_us     = esp_timer_get_time();
  const int64_t elapsed_us = now_us - last_update_us_;
  if (last_update_us_ != 0 &&
      elapsed_us < static_cast<int64_t>(kMinUpdateIntervalMs) * 1000LL) {
    return true;  // Throttled — not an error.
  }

  // Read Flags() first to assess data validity before publishing values.
  uint16_t flags = 0;
  esp_err_t ret = ReadWord(kCmdFlags, &flags);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to read Flags(): %s", esp_err_to_name(ret));
    return false;
  }
  flags_ = flags;

  // [ITPOR] set means RAM was just reset — readings not yet meaningful.
  // [CFGUPMODE] means gauging is suspended for configuration.
  // [BAT_DET] must be set for active measurement.
  const bool itpor      = (flags & kFlagItpor)     != 0;
  const bool cfgupmode  = (flags & (1 << 12))      != 0;
  const bool bat_detect = (flags & kFlagBatDetect) != 0;
  data_valid_ = bat_detect && !itpor && !cfgupmode;

  if (!data_valid_) {
    ESP_LOGD(kTag, "Gauge not yet in NORMAL mode "
             "(Flags=0x%04X ITPOR=%d CFGUP=%d BAT_DET=%d)",
             flags, itpor, cfgupmode, bat_detect);
    last_update_us_ = now_us;
    return true;  // Not an I2C error — gauge is still initializing.
  }

  int16_t avg_power = 0;
  ret = ReadWordSigned(kCmdAveragePower, &avg_power);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to read AveragePower(): %s", esp_err_to_name(ret));
    return false;
  }

  uint16_t soc = 0;
  ret = ReadWord(kCmdStateOfCharge, &soc);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to read StateOfCharge(): %s", esp_err_to_name(ret));
    return false;
  }

  average_power_mw_    = avg_power;
  state_of_charge_pct_ = soc;
  last_update_us_      = now_us;
  return true;
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

esp_err_t Bq27427::WriteSubCmd(uint16_t subcmd) {
  uint8_t buf[3] = {
    kCmdControl,
    static_cast<uint8_t>(subcmd & 0xFF),
    static_cast<uint8_t>(subcmd >> 8),
  };
  return i2c_master_transmit(i2c_handle_, buf, sizeof(buf), -1);
}

esp_err_t Bq27427::ReadWord(uint8_t cmd, uint16_t* out) {
  uint8_t buf[2] = {};
  esp_err_t ret = i2c_master_transmit_receive(i2c_handle_, &cmd, 1,
                                               buf, sizeof(buf), -1);
  if (ret != ESP_OK) return ret;
  *out = static_cast<uint16_t>(buf[0]) | (static_cast<uint16_t>(buf[1]) << 8);
  return ESP_OK;
}

esp_err_t Bq27427::ReadWordSigned(uint8_t cmd, int16_t* out) {
  uint16_t raw = 0;
  esp_err_t ret = ReadWord(cmd, &raw);
  if (ret != ESP_OK) return ret;
  static_assert(sizeof(int16_t) == sizeof(uint16_t), "size mismatch");
  __builtin_memcpy(out, &raw, sizeof(raw));
  return ESP_OK;
}
