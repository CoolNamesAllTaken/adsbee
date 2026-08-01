#include "fxl6408.hh"

#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

static const char* kTag = "FXL6408";

// ---------------------------------------------------------------------------
// Static member definitions
// ---------------------------------------------------------------------------
gpio_num_t        Fxl6408::s_int_pin_        = GPIO_NUM_NC;
bool              Fxl6408::s_isr_installed_  = false;
Fxl6408*          Fxl6408::s_instance_list_  = nullptr;
SemaphoreHandle_t Fxl6408::s_instance_mutex_ = nullptr;
Fxl6408*          Fxl6408::s_registry_[Fxl6408::kNumExpanders] = {};

// ---------------------------------------------------------------------------
// Constructor / Destructor
// ---------------------------------------------------------------------------

Fxl6408::Fxl6408(const Config& config)
    : config_(config),
      i2c_handle_(nullptr),
      owned_bus_handle_(nullptr),
      int_sem_(nullptr),
      next_instance_(nullptr) {
  if (s_instance_mutex_ == nullptr) {
    s_instance_mutex_ = xSemaphoreCreateMutex();
  }
}

Fxl6408::~Fxl6408() {
  if (i2c_handle_ != nullptr) {
    Deinit();
  }
  if (int_sem_ != nullptr) {
    vSemaphoreDelete(int_sem_);
    int_sem_ = nullptr;
  }
}

// ---------------------------------------------------------------------------
// Shared ISR
// ---------------------------------------------------------------------------

void IRAM_ATTR Fxl6408::SharedIsrHandler(void* /*arg*/) {
  BaseType_t higher_priority_task_woken = pdFALSE;
  for (Fxl6408* inst = s_instance_list_; inst != nullptr; inst = inst->next_instance_) {
    if (inst->int_sem_ != nullptr) {
      xSemaphoreGiveFromISR(inst->int_sem_, &higher_priority_task_woken);
    }
  }
  portYIELD_FROM_ISR(higher_priority_task_woken);
}

// ---------------------------------------------------------------------------
// Shared GPIO control
// ---------------------------------------------------------------------------

bool Fxl6408::HardwareReset(gpio_num_t reset_pin) {
  gpio_config_t io_cfg   = {};
  io_cfg.pin_bit_mask    = 1ULL << reset_pin;
  io_cfg.mode            = GPIO_MODE_OUTPUT;
  io_cfg.pull_up_en      = GPIO_PULLUP_DISABLE;
  io_cfg.pull_down_en    = GPIO_PULLDOWN_DISABLE;
  io_cfg.intr_type       = GPIO_INTR_DISABLE;
  esp_err_t ret = gpio_config(&io_cfg);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "gpio_config for RESET pin failed: %s", esp_err_to_name(ret));
    return false;
  }

  // Active-low reset: assert for at least 1 µs (datasheet §6.3); 5 ms for margin.
  gpio_set_level(reset_pin, 0);
  vTaskDelay(pdMS_TO_TICKS(5));
  gpio_set_level(reset_pin, 1);
  vTaskDelay(pdMS_TO_TICKS(1));

  ESP_LOGI(kTag, "Hardware reset pulsed on GPIO %d", reset_pin);
  return true;
}


// ---------------------------------------------------------------------------
// Instance list helpers
// ---------------------------------------------------------------------------

void Fxl6408::RegisterInstance() {
  xSemaphoreTake(s_instance_mutex_, portMAX_DELAY);
  next_instance_ = s_instance_list_;
  s_instance_list_ = this;
  xSemaphoreGive(s_instance_mutex_);
}

void Fxl6408::UnregisterInstance() {
  xSemaphoreTake(s_instance_mutex_, portMAX_DELAY);
  if (s_instance_list_ == this) {
    s_instance_list_ = next_instance_;
  } else {
    for (Fxl6408* prev = s_instance_list_; prev != nullptr; prev = prev->next_instance_) {
      if (prev->next_instance_ == this) {
        prev->next_instance_ = next_instance_;
        break;
      }
    }
  }
  next_instance_ = nullptr;
  xSemaphoreGive(s_instance_mutex_);
}

// ---------------------------------------------------------------------------
// Lifecycle
// ---------------------------------------------------------------------------

bool Fxl6408::Init() {
  if (i2c_handle_ != nullptr) {
    ESP_LOGW(kTag, "Already initialized (addr=0x%02X) — call Deinit() first",
             config_.i2c_address);
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
  dev_cfg.dev_addr_length  = I2C_ADDR_BIT_LEN_7;
  dev_cfg.device_address   = config_.i2c_address;
  dev_cfg.scl_speed_hz     = config_.i2c_speed_hz;

  esp_err_t ret = i2c_master_bus_add_device(bus, &dev_cfg, &i2c_handle_);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to add I2C device (addr=0x%02X): %s",
             config_.i2c_address, esp_err_to_name(ret));
    i2c_handle_ = nullptr;
    if (owned_bus_handle_ != nullptr) {
      i2c_del_master_bus(owned_bus_handle_);
      owned_bus_handle_ = nullptr;
    }
    return false;
  }

  // Verify device identity.
  uint8_t dev_id = 0;
  ret = ReadReg(kRegDeviceId, &dev_id);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to read device ID: %s", esp_err_to_name(ret));
    Deinit();
    return false;
  }
  if ((dev_id & kDeviceIdMask) != kDeviceIdExpected) {
    ESP_LOGE(kTag, "Unexpected device ID: 0x%02X (expected 0x%02X masked with 0x%02X)",
             dev_id, kDeviceIdExpected, kDeviceIdMask);
    Deinit();
    return false;
  }

  // Create per-instance interrupt semaphore before registering in the list.
  int_sem_ = xSemaphoreCreateBinary();
  if (int_sem_ == nullptr) {
    ESP_LOGE(kTag, "Failed to create interrupt semaphore");
    Deinit();
    return false;
  }

  ret = ApplyPinConfig(config_.pins);
  if (ret != ESP_OK) {
    Deinit();
    return false;
  }

  // Install the shared ISR on first use; subsequent instances reuse it.
  if (config_.int_pin != GPIO_NUM_NC) {
    if (s_isr_installed_ && s_int_pin_ != config_.int_pin) {
      ESP_LOGE(kTag, "ISR already installed on GPIO %d, cannot reuse for GPIO %d",
               s_int_pin_, config_.int_pin);
      Deinit();
      return false;
    }
    if (!s_isr_installed_) {
      gpio_config_t io_cfg   = {};
      io_cfg.pin_bit_mask    = 1ULL << config_.int_pin;
      io_cfg.mode            = GPIO_MODE_INPUT;
      io_cfg.pull_up_en      = GPIO_PULLUP_ENABLE;
      io_cfg.pull_down_en    = GPIO_PULLDOWN_DISABLE;
      io_cfg.intr_type       = GPIO_INTR_NEGEDGE;
      ret = gpio_config(&io_cfg);
      if (ret != ESP_OK) {
        ESP_LOGE(kTag, "gpio_config for INT pin failed: %s", esp_err_to_name(ret));
        Deinit();
        return false;
      }
      ret = gpio_isr_handler_add(config_.int_pin, SharedIsrHandler, nullptr);
      if (ret != ESP_OK) {
        ESP_LOGE(kTag, "gpio_isr_handler_add failed: %s", esp_err_to_name(ret));
        Deinit();
        return false;
      }
      s_int_pin_       = config_.int_pin;
      s_isr_installed_ = true;
      ESP_LOGI(kTag, "Shared ISR installed on GPIO %d", config_.int_pin);
    }
  }

  RegisterInstance();

  // Register in the global address-indexed registry.
  uint8_t idx = (config_.i2c_address == kI2cAddressAddrLow) ? 0 : 1;
  s_registry_[idx] = this;

  ESP_LOGI(kTag, "Initialized (addr=0x%02X, dev_id=0x%02X)",
           config_.i2c_address, dev_id);
  return true;
}

bool Fxl6408::Deinit() {
  if (i2c_handle_ == nullptr) {
    return true;
  }

  UnregisterInstance();

  uint8_t idx = (config_.i2c_address == kI2cAddressAddrLow) ? 0 : 1;
  s_registry_[idx] = nullptr;

  if (int_sem_ != nullptr) {
    vSemaphoreDelete(int_sem_);
    int_sem_ = nullptr;
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

  ESP_LOGI(kTag, "Deinitialized (addr=0x%02X)", config_.i2c_address);
  return ok;
}

// ---------------------------------------------------------------------------
// I/O
// ---------------------------------------------------------------------------

bool Fxl6408::ReadInputs(uint8_t* value) {
  return ReadReg(kRegInputStatus, value) == ESP_OK;
}

bool Fxl6408::WriteOutputs(uint8_t value) {
  return WriteReg(kRegOutput, value) == ESP_OK;
}

bool Fxl6408::SetPin(uint8_t pin, bool level) {
  if (pin > 7) {
    ESP_LOGE(kTag, "SetPin: pin %u out of range", pin);
    return false;
  }
  uint8_t current = 0;
  if (ReadReg(kRegOutput, &current) != ESP_OK) return false;
  if (level) {
    current |=  (1u << pin);
  } else {
    current &= ~(1u << pin);
  }
  return WriteReg(kRegOutput, current) == ESP_OK;
}

bool Fxl6408::ReadInterruptStatus(uint8_t* status) {
  return ReadReg(kRegInterruptStatus, status) == ESP_OK;
}

esp_err_t Fxl6408::WaitForInterrupt(uint32_t timeout_ms) {
  if (int_sem_ == nullptr) {
    return ESP_ERR_INVALID_STATE;
  }
  TickType_t ticks = (timeout_ms == portMAX_DELAY)
                     ? portMAX_DELAY
                     : pdMS_TO_TICKS(timeout_ms);
  return (xSemaphoreTake(int_sem_, ticks) == pdTRUE) ? ESP_OK : ESP_ERR_TIMEOUT;
}

bool Fxl6408::ConfigurePins(const PinConfig pins[8]) {
  return ApplyPinConfig(pins) == ESP_OK;
}

// ---------------------------------------------------------------------------
// Global pin access
// ---------------------------------------------------------------------------

bool Fxl6408::ConfigurePin(fxl6408_pin_t pin, const PinConfig& cfg) {
  uint8_t idx = FXL6408_PIN_EXPANDER(pin);
  if (idx >= kNumExpanders || s_registry_[idx] == nullptr) {
    ESP_LOGE(kTag, "ConfigurePin: expander %u not initialized", idx);
    return false;
  }
  Fxl6408* inst = s_registry_[idx];
  uint8_t  bit  = static_cast<uint8_t>(1u << FXL6408_PIN_NUMBER(pin));

  // Read-modify-write each affected register.
  auto rmw = [&](uint8_t reg, bool set) -> bool {
    uint8_t val = 0;
    if (inst->ReadReg(reg, &val) != ESP_OK) return false;
    if (set) { val |= bit; } else { val &= ~bit; }
    return inst->WriteReg(reg, val) == ESP_OK;
  };

  if (!rmw(kRegIoDir,       cfg.direction == Direction::kOutput)) return false;
  if (!rmw(kRegOutputHighZ, cfg.direction != Direction::kOutput)) return false;
  if (!rmw(kRegPullEnable,  cfg.pull != PullMode::kNone))         return false;
  if (!rmw(kRegPullDir,     cfg.pull == PullMode::kPullUp))       return false;
  if (cfg.direction == Direction::kOutput && cfg.initial_out) {
    if (!rmw(kRegOutput, true)) return false;
  }
  // Clear interrupt status for this pin.
  uint8_t dummy = 0;
  inst->ReadReg(kRegInterruptStatus, &dummy);
  return true;
}

bool Fxl6408::WritePin(fxl6408_pin_t pin, bool level) {
  uint8_t idx = FXL6408_PIN_EXPANDER(pin);
  if (idx >= kNumExpanders || s_registry_[idx] == nullptr) {
    ESP_LOGE(kTag, "WritePin: expander %u not initialized", idx);
    return false;
  }
  return s_registry_[idx]->SetPin(FXL6408_PIN_NUMBER(pin), level);
}

bool Fxl6408::ReadPin(fxl6408_pin_t pin, bool* level) {
  uint8_t idx = FXL6408_PIN_EXPANDER(pin);
  if (idx >= kNumExpanders || s_registry_[idx] == nullptr) {
    ESP_LOGE(kTag, "ReadPin: expander %u not initialized", idx);
    return false;
  }
  uint8_t inputs = 0;
  if (!s_registry_[idx]->ReadInputs(&inputs)) return false;
  *level = (inputs >> FXL6408_PIN_NUMBER(pin)) & 0x1;
  return true;
}

// ---------------------------------------------------------------------------
// Register access
// ---------------------------------------------------------------------------

esp_err_t Fxl6408::WriteReg(uint8_t reg, uint8_t value) {
  uint8_t buf[2] = {reg, value};
  esp_err_t ret = i2c_master_transmit(i2c_handle_, buf, sizeof(buf), -1);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "WriteReg 0x%02X failed: %s", reg, esp_err_to_name(ret));
  }
  return ret;
}

esp_err_t Fxl6408::ReadReg(uint8_t reg, uint8_t* value) {
  esp_err_t ret = i2c_master_transmit_receive(i2c_handle_, &reg, 1, value, 1, -1);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "ReadReg 0x%02X failed: %s", reg, esp_err_to_name(ret));
  }
  return ret;
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

esp_err_t Fxl6408::ApplyPinConfig(const PinConfig pins[8]) {
  uint8_t io_dir       = 0x00;
  uint8_t output_val   = 0x00;
  uint8_t output_hiz   = 0xFF;
  uint8_t pull_en      = 0x00;
  uint8_t pull_dir     = 0x00;
  uint8_t int_mask     = 0xFF;

  for (uint8_t i = 0; i < 8; i++) {
    const PinConfig& p = pins[i];
    const uint8_t    b = static_cast<uint8_t>(1u << i);

    if (p.direction == Direction::kOutput) {
      io_dir |= b;
      output_hiz &= ~b;
      if (p.initial_out) output_val |= b;
    }

    if (p.pull != PullMode::kNone) {
      pull_en |= b;
      if (p.pull == PullMode::kPullUp) pull_dir |= b;
    }

    if (p.int_enable && p.direction == Direction::kInput) {
      int_mask &= ~b;
    }
  }

  esp_err_t ret;
  if ((ret = WriteReg(kRegIoDir,         io_dir))     != ESP_OK) return ret;
  if ((ret = WriteReg(kRegOutput,        output_val)) != ESP_OK) return ret;
  if ((ret = WriteReg(kRegOutputHighZ,   output_hiz)) != ESP_OK) return ret;
  if ((ret = WriteReg(kRegPullEnable,    pull_en))    != ESP_OK) return ret;
  if ((ret = WriteReg(kRegPullDir,       pull_dir))   != ESP_OK) return ret;
  if ((ret = WriteReg(kRegInterruptMask, int_mask))   != ESP_OK) return ret;

  uint8_t dummy = 0;
  return ReadReg(kRegInterruptStatus, &dummy);
}
