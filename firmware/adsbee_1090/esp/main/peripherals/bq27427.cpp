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

  // Program the cell specs (Design Capacity / Terminate Voltage / chemistry) so
  // the Impedance-Track SOC estimate is accurate. Non-fatal: on failure the
  // gauge keeps its current config and still reports (less accurate) values.
  if (config_.configure_battery) {
    ConfigureBattery();
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
  const bool itpor      = (flags & kFlagItpor)      != 0;
  const bool cfgupmode  = (flags & kFlagCfgUpMode)  != 0;  // CFGUPMODE = bit 4 (TRM Table 5-4)
  const bool bat_detect = (flags & kFlagBatDetect)  != 0;
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

  // Remaining capacity + average current, used to estimate time-to-empty.
  uint16_t rem_cap = 0;
  ret = ReadWord(kCmdRemCapacity, &rem_cap);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to read RemainingCapacity(): %s", esp_err_to_name(ret));
    return false;
  }
  int16_t avg_current = 0;
  ret = ReadWordSigned(kCmdAverageCurrent, &avg_current);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to read AverageCurrent(): %s", esp_err_to_name(ret));
    return false;
  }

  average_power_mw_       = avg_power;
  state_of_charge_pct_    = soc;
  remaining_capacity_mah_ = rem_cap;
  average_current_ma_     = avg_current;
  last_update_us_         = now_us;
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

esp_err_t Bq27427::WriteByte(uint8_t cmd, uint8_t value) {
  uint8_t buf[2] = {cmd, value};
  return i2c_master_transmit(i2c_handle_, buf, sizeof(buf), -1);
}

esp_err_t Bq27427::ReadByte(uint8_t cmd, uint8_t* out) {
  return i2c_master_transmit_receive(i2c_handle_, &cmd, 1, out, 1, -1);
}

esp_err_t Bq27427::WaitFlag(uint16_t mask, bool set, uint32_t timeout_ms) {
  const int64_t deadline = esp_timer_get_time() + (int64_t)timeout_ms * 1000LL;
  while (esp_timer_get_time() < deadline) {
    uint16_t flags = 0;
    esp_err_t ret = ReadWord(kCmdFlags, &flags);
    if (ret != ESP_OK) return ret;
    if (((flags & mask) != 0) == set) return ESP_OK;
    vTaskDelay(pdMS_TO_TICKS(25));
  }
  return ESP_ERR_TIMEOUT;
}

// ---------------------------------------------------------------------------
// Battery configuration (CONFIG UPDATE flow, TRM Section 4)
// ---------------------------------------------------------------------------

esp_err_t Bq27427::Unseal() {
  // The UNSEAL key is the same 0x8000 word sent twice.
  esp_err_t ret = WriteSubCmd(kSubCmdUnseal);
  if (ret != ESP_OK) return ret;
  return WriteSubCmd(kSubCmdUnseal);
}

esp_err_t Bq27427::SelectChemProfile(uint8_t profile) {
  uint16_t subcmd;
  switch (profile) {
    case 0:  subcmd = kSubCmdChemA; break;
    case 1:  subcmd = kSubCmdChemB; break;
    case 2:  subcmd = kSubCmdChemC; break;
    default: return ESP_ERR_INVALID_ARG;
  }
  return WriteSubCmd(subcmd);
}

// Read a big-endian int16 parameter from the currently-selected 32-byte block.
// Block data (unlike standard commands) is MSB-first.
esp_err_t Bq27427::ReadStateParam(uint8_t offset, int16_t* out) {
  uint8_t msb = 0, lsb = 0;
  esp_err_t ret = ReadByte(kCmdBlockData + (offset % 32), &msb);
  if (ret != ESP_OK) return ret;
  ret = ReadByte(kCmdBlockData + (offset % 32) + 1, &lsb);
  if (ret != ESP_OK) return ret;
  *out = (int16_t)(((uint16_t)msb << 8) | lsb);
  return ESP_OK;
}

// Write a big-endian int16 into the current block and fix up the block checksum.
// The block (State subclass 0x52, block 0) must already be selected and in
// CONFIG UPDATE mode. Checksum = 255 − (sum of all 32 block bytes mod 256);
// we use the TRM's incremental data-replacement formula so we only touch the
// two changed bytes.
esp_err_t Bq27427::WriteStateParam(uint8_t offset, int16_t value) {
  const uint8_t addr = kCmdBlockData + (offset % 32);
  uint8_t old_csum = 0;
  esp_err_t ret = ReadByte(kCmdBlockDataChecksum, &old_csum);
  if (ret != ESP_OK) return ret;

  uint8_t old_msb = 0, old_lsb = 0;
  ret = ReadByte(addr, &old_msb);
  if (ret != ESP_OK) return ret;
  ret = ReadByte(addr + 1, &old_lsb);
  if (ret != ESP_OK) return ret;

  const uint8_t new_msb = (uint8_t)((uint16_t)value >> 8);
  const uint8_t new_lsb = (uint8_t)((uint16_t)value & 0xFF);

  // Incremental checksum (TRM Section 4.1 step 10 formula).
  uint8_t temp = (uint8_t)((255 - old_csum - old_msb - old_lsb) % 256);
  uint8_t new_csum = (uint8_t)(255 - ((temp + new_msb + new_lsb) % 256));

  ret = WriteByte(addr, new_msb);
  if (ret != ESP_OK) return ret;
  ret = WriteByte(addr + 1, new_lsb);
  if (ret != ESP_OK) return ret;
  return WriteByte(kCmdBlockDataChecksum, new_csum);
}

bool Bq27427::ConfigureBattery() {
  // 1. Unseal.
  if (Unseal() != ESP_OK) {
    ESP_LOGW(kTag, "Battery config: UNSEAL failed");
    return false;
  }

  // 2. Check whether the chemistry already matches; only change if needed.
  const uint16_t want_chem = (config_.chem_profile == 0)   ? kChemIdA
                             : (config_.chem_profile == 1) ? kChemIdB
                                                           : kChemIdC;
  uint16_t cur_chem = 0;
  if (WriteSubCmd(kSubCmdChemId) == ESP_OK) ReadWord(kCmdControl, &cur_chem);
  bool chem_changed = (cur_chem != want_chem);

  // 3. Enter CONFIG UPDATE mode.
  if (WriteSubCmd(kSubCmdSetCfgUpdate) != ESP_OK ||
      WaitFlag(kFlagCfgUpMode, /*set=*/true, /*timeout_ms=*/2000) != ESP_OK) {
    ESP_LOGW(kTag, "Battery config: entering CONFIG UPDATE failed");
    return false;
  }

  bool ok = true;

  // 4. Chemistry (if needed) — no block-data write.
  if (chem_changed) {
    if (SelectChemProfile(config_.chem_profile) == ESP_OK) {
      ESP_LOGI(kTag, "Chem profile -> %u (was %u)", want_chem, cur_chem);
    } else {
      ESP_LOGW(kTag, "Chem profile select failed");
      ok = false;
    }
  } else {
    ESP_LOGI(kTag, "Chem profile already %u — skip", cur_chem);
  }

  // 5. Select the State subclass, block 0, for Design Capacity / Terminate Voltage.
  if (WriteByte(kCmdBlockDataControl, 0x00) == ESP_OK &&
      WriteByte(kCmdDataClass, kDmStateSubclass) == ESP_OK &&
      WriteByte(kCmdDataBlock, 0x00) == ESP_OK) {
    vTaskDelay(pdMS_TO_TICKS(5));  // let the block load

    // Design Capacity (offset 6). Write only if different.
    int16_t cur = 0;
    if (ReadStateParam(kDmDesignCapacityOffset, &cur) == ESP_OK) {
      if (cur != (int16_t)config_.design_capacity_mah) {
        if (WriteStateParam(kDmDesignCapacityOffset,
                            (int16_t)config_.design_capacity_mah) == ESP_OK) {
          ESP_LOGI(kTag, "Design Capacity -> %u mAh (was %d)",
                   config_.design_capacity_mah, cur);
        } else { ok = false; }
      } else {
        ESP_LOGI(kTag, "Design Capacity already %d mAh — skip", cur);
      }
    }

    // Terminate Voltage (offset 10). Write only if different.
    if (ReadStateParam(kDmTerminateVoltageOffset, &cur) == ESP_OK) {
      if (cur != (int16_t)config_.terminate_voltage_mv) {
        if (WriteStateParam(kDmTerminateVoltageOffset,
                            (int16_t)config_.terminate_voltage_mv) == ESP_OK) {
          ESP_LOGI(kTag, "Terminate Voltage -> %u mV (was %d)",
                   config_.terminate_voltage_mv, cur);
        } else { ok = false; }
      } else {
        ESP_LOGI(kTag, "Terminate Voltage already %d mV — skip", cur);
      }
    }
  } else {
    ESP_LOGW(kTag, "Battery config: block select failed");
    ok = false;
  }

  // 6. Exit CONFIG UPDATE via SOFT_RESET; wait for CFGUPMODE to clear.
  if (WriteSubCmd(kSubCmdSoftReset) != ESP_OK ||
      WaitFlag(kFlagCfgUpMode, /*set=*/false, /*timeout_ms=*/2000) != ESP_OK) {
    ESP_LOGW(kTag, "Battery config: SOFT_RESET / exit failed");
    ok = false;
  }

  // 7. Re-seal.
  if (WriteSubCmd(kSubCmdSealed) != ESP_OK) {
    ESP_LOGW(kTag, "Battery config: re-SEAL failed");
  }

  ESP_LOGI(kTag, "Battery configuration %s", ok ? "complete" : "completed with warnings");
  return ok;
}
