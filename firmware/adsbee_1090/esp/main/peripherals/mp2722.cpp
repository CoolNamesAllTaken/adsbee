#include "mp2722.hh"

#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

static const char* kTag = "MP2722";

// ---------------------------------------------------------------------------
// Constructor / Destructor
// ---------------------------------------------------------------------------

Mp2722::Mp2722(const Config& config)
    : config_(config),
      i2c_handle_(nullptr),
      owned_bus_handle_(nullptr),
      power_good_(false),
      is_charging_(false),
      thermal_regulation_(false),
      watchdog_fault_(false),
      chg_fault_(0),
      boost_fault_(0),
      charge_status_(ChargeStatus::kNotCharging),
      raw_vin_stat_(0),
      raw_chg_fault_stat_(0) {}

Mp2722::~Mp2722() {
  if (i2c_handle_ != nullptr) {
    Deinit();
  }
}

// ---------------------------------------------------------------------------
// Lifecycle
// ---------------------------------------------------------------------------

bool Mp2722::Init() {
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

  vTaskDelay(pdMS_TO_TICKS(kStartupTimeMs));

  // Per the datasheet (p. 22): WATCHDOG_FAULT starts set at every power-on.
  // Pulsing WATCHDOG_RST clears the fault latch, even when disabling the timer.
  ret = ModifyReg(kRegWatchdogTimer, kWatchdogRstBit, kWatchdogRstBit);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to clear watchdog fault latch: %s", esp_err_to_name(ret));
    Deinit();
    return false;
  }

  if (config_.disable_watchdog) {
    // Timer has started (WATCHDOG_RST pulse); now disable it so it never expires.
    ret = ModifyReg(kRegWatchdogTimer, kWatchdogMask, kWatchdogDisable);
    if (ret != ESP_OK) {
      ESP_LOGE(kTag, "Failed to disable watchdog: %s", esp_err_to_name(ret));
      Deinit();
      return false;
    }
    ESP_LOGI(kTag, "Watchdog timer disabled");
  }

  if (!Update()) {
    ESP_LOGE(kTag, "Initial status read failed");
    Deinit();
    return false;
  }

  ESP_LOGI(kTag, "Initialized — VIN_GD:%d CHG_STAT:%u CHG_FAULT:0x%02X BOOST_FAULT:0x%02X",
           power_good_,
           static_cast<uint8_t>(charge_status_),
           chg_fault_,
           boost_fault_);
  return true;
}

bool Mp2722::Deinit() {
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
// Control
// ---------------------------------------------------------------------------

bool Mp2722::Update() {
  uint8_t vin_stat = 0;
  esp_err_t ret = ReadReg(kRegVinStat, &vin_stat);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to read REG12h: %s", esp_err_to_name(ret));
    return false;
  }

  uint8_t chg_fault_stat = 0;
  ret = ReadReg(kRegChgFaultStat, &chg_fault_stat);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to read REG13h: %s", esp_err_to_name(ret));
    return false;
  }

  raw_vin_stat_       = vin_stat;
  raw_chg_fault_stat_ = chg_fault_stat;

  ParseStatus(vin_stat, chg_fault_stat);
  return true;
}

bool Mp2722::KickWatchdog() {
  return ModifyReg(kRegWatchdogTimer, kWatchdogRstBit, kWatchdogRstBit) == ESP_OK;
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

esp_err_t Mp2722::WriteReg(uint8_t reg, uint8_t value) {
  uint8_t buf[2] = {reg, value};
  return i2c_master_transmit(i2c_handle_, buf, sizeof(buf), -1);
}

esp_err_t Mp2722::ReadReg(uint8_t reg, uint8_t* value) {
  return i2c_master_transmit_receive(i2c_handle_, &reg, 1, value, 1, -1);
}

esp_err_t Mp2722::ModifyReg(uint8_t reg, uint8_t mask, uint8_t value) {
  uint8_t current = 0;
  esp_err_t ret = ReadReg(reg, &current);
  if (ret != ESP_OK) return ret;
  current = (current & ~mask) | (value & mask);
  return WriteReg(reg, current);
}

void Mp2722::ParseStatus(uint8_t vin_stat, uint8_t chg_fault_stat) {
  power_good_         = (vin_stat & kVinGdMask)         != 0;
  thermal_regulation_ = (vin_stat & kThermStatMask)     != 0;
  watchdog_fault_     = (vin_stat & kWatchdogFaultMask) != 0;

  uint8_t chg_raw = (chg_fault_stat & kChgStatMask)    >> kChgStatShift;
  boost_fault_     = (chg_fault_stat & kBoostFaultMask) >> kBoostFaultShift;
  chg_fault_       = (chg_fault_stat & kChgFaultMask)   >> kChgFaultShift;

  switch (chg_raw) {
    case kChgStatTrickle:    charge_status_ = ChargeStatus::kTrickle;     break;
    case kChgStatPreCharge:  charge_status_ = ChargeStatus::kPreCharge;   break;
    case kChgStatFastCharge: charge_status_ = ChargeStatus::kFastCharge;  break;
    case kChgStatCvCharge:   charge_status_ = ChargeStatus::kCvCharge;    break;
    case kChgStatDone:       charge_status_ = ChargeStatus::kDone;        break;
    default:                 charge_status_ = ChargeStatus::kNotCharging; break;
  }

  is_charging_ = power_good_ &&
                 (charge_status_ == ChargeStatus::kTrickle    ||
                  charge_status_ == ChargeStatus::kPreCharge  ||
                  charge_status_ == ChargeStatus::kFastCharge ||
                  charge_status_ == ChargeStatus::kCvCharge);

  if (watchdog_fault_) {
    ESP_LOGW(kTag, "Watchdog timer expired (REG12h=0x%02X)", vin_stat);
  }
  if (chg_fault_ != 0) {
    ESP_LOGW(kTag, "Charge fault: CHG_FAULT=0x%X (%s)",
             chg_fault_,
             chg_fault_ == kChgFaultInputOvp    ? "Input OVP"     :
             chg_fault_ == kChgFaultTimerExpired ? "Timer expired" :
             chg_fault_ == kChgFaultBattOvp      ? "Battery OVP"   : "Unknown");
  }
  if (boost_fault_ != 0) {
    ESP_LOGW(kTag, "Boost fault: BOOST_FAULT=0x%X", boost_fault_);
  }
}
