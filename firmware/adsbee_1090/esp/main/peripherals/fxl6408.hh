#pragma once

#include <cstdint>
#include <functional>
#include "driver/gpio.h"
#include "driver/i2c_master.h"
#include "esp_err.h"
#include "freertos/FreeRTOS.h"
#include "freertos/semphr.h"
#include "bsp.hh"
#include "peripherals/fxl6408_pin_config.hh"  // fxl6408_pin_t, FXL6408_PIN macros

// FXL6408 8-bit I2C GPIO Expander Driver
// Datasheet: NXP FXL6408, Rev. 2.1
//
// Two expanders can share a single interrupt line and a single reset line.
// Set Config::int_pin on any instance; Init() installs the shared ISR on first
// use and all instances receive notifications when it fires.
// Call Fxl6408::HardwareReset() to pulse the shared reset line.

class Fxl6408 {
 public:
  // I2C address — ADDR pin low = 0x43, high = 0x44
  static constexpr uint8_t kI2cAddressAddrLow  = 0x43;
  static constexpr uint8_t kI2cAddressAddrHigh = 0x44;

  // -------------------------------------------------------------------------
  // Register map
  // -------------------------------------------------------------------------
  static constexpr uint8_t kRegDeviceId         = 0x01;  // R   Device ID / revision
  static constexpr uint8_t kRegIoDir            = 0x03;  // R/W 0=input, 1=output  (default 0xFF)
  static constexpr uint8_t kRegOutput           = 0x05;  // R/W Output state for pins configured as outputs
  static constexpr uint8_t kRegOutputHighZ      = 0x07;  // R/W 1=Hi-Z output, 0=driven         (default 0xFF)
  static constexpr uint8_t kRegInputDefaultState = 0x09; // R/W Expected / default input state
  static constexpr uint8_t kRegPullEnable        = 0x0B; // R/W 1=pull enabled
  static constexpr uint8_t kRegPullDir           = 0x0D; // R/W 0=pull-down, 1=pull-up
  static constexpr uint8_t kRegInputStatus       = 0x0F; // R   Live input state (read clears INT for inputs)
  static constexpr uint8_t kRegInterruptMask     = 0x11; // R/W 1=masked (no interrupt on change)
  static constexpr uint8_t kRegInterruptStatus   = 0x13; // R   1=interrupt pending on that pin (read-to-clear)

  // -------------------------------------------------------------------------
  // Device-ID register expected value.
  // Reset value is 0xA2 (0b10100010). Bits [1:0] are the revision field and
  // may vary between silicon revisions, so mask them out before comparing.
  // bits [7:2] = 0b101000 = 0x28; masked full byte = 0xA0.
  // -------------------------------------------------------------------------
  static constexpr uint8_t kDeviceIdMask     = 0xFC;
  static constexpr uint8_t kDeviceIdExpected = 0xA0;  // 0x28 in bits [7:2]

  // -------------------------------------------------------------------------
  // Pin direction / pull configuration
  // -------------------------------------------------------------------------
  enum class Direction : uint8_t { kOutput = 0, kInput = 1 };
  enum class PullMode  : uint8_t { kNone = 0, kPullDown = 1, kPullUp = 2 };

  struct PinConfig {
    Direction direction   = Direction::kInput;
    PullMode  pull        = PullMode::kNone;
    bool      initial_out = false;  // Initial output level (ignored for inputs)
    bool      int_enable  = false;  // Assert shared INT on change (inputs only)
  };

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

    // 7-bit I2C address (kI2cAddressAddrLow or kI2cAddressAddrHigh).
    uint8_t i2c_address = kI2cAddressAddrLow;

    // I2C clock speed (Hz). FXL6408 supports up to 400 kHz.
    uint32_t i2c_speed_hz = 400000;

    // Active-low interrupt input pin shared across all expander instances.
    // Init() installs the ISR on first use; subsequent instances reuse it.
    // Set to GPIO_NUM_NC to disable interrupt support for this instance.
    gpio_num_t int_pin = bsp.periph_i2c_expander_int_pin;

    // Per-pin configuration array, index 0 = GPIO0 … index 7 = GPIO7.
    PinConfig pins[8] = {};
  };

  explicit Fxl6408(const Config& config);
  ~Fxl6408();

  Fxl6408(const Fxl6408&)            = delete;
  Fxl6408& operator=(const Fxl6408&) = delete;

  // ---------------------------------------------------------------------------
  // Shared GPIO control — call these once before Init()-ing any instance.
  // ---------------------------------------------------------------------------

  // Pulses the shared active-low reset line (≥ 1 ms low per datasheet).
  // This resets all expanders sharing the line simultaneously.
  static bool HardwareReset(gpio_num_t reset_pin = bsp.periph_i2c_expander_reset_pin);

  // ---------------------------------------------------------------------------
  // Global pin access via encoded fxl6408_pin_t handle.
  // Expander index is derived from I2C address: AddrLow=0, AddrHigh=1.
  // Init() registers each instance in the global registry; these are safe to
  // call on any thread after the relevant expander has been initialized.
  // ---------------------------------------------------------------------------
  static bool ConfigurePin(fxl6408_pin_t pin, const PinConfig& config);
  static bool WritePin(fxl6408_pin_t pin, bool level);
  static bool ReadPin(fxl6408_pin_t pin, bool* level);

  // ---------------------------------------------------------------------------
  // Lifecycle
  // ---------------------------------------------------------------------------

  // Registers the I2C device, verifies the device ID, applies the pin
  // configuration from Config::pins[], and installs the shared ISR if
  // Config::int_pin is set and not yet installed.
  bool Init();

  // Removes the device from the bus and unregisters from interrupt delivery.
  // If this driver created the bus, it is deleted.
  bool Deinit();

  bool IsInitialized() const { return i2c_handle_ != nullptr; }

  // ---------------------------------------------------------------------------
  // I/O (call only after Init())
  // ---------------------------------------------------------------------------

  // Reads the live input state of all 8 pins into *value (bit N = GPIO N).
  // Also clears any pending interrupt flags for input pins.
  bool ReadInputs(uint8_t* value);

  // Writes the output latch for output-configured pins. Bits corresponding
  // to input-configured pins are ignored by the hardware.
  bool WriteOutputs(uint8_t value);

  // Sets or clears a single output pin. pin must be 0–7.
  bool SetPin(uint8_t pin, bool level);

  // Reads the interrupt-status register (read-to-clear). Bits set indicate
  // a change occurred on the corresponding input since the last read.
  bool ReadInterruptStatus(uint8_t* status);

  // Applies a full direction / pull / output / interrupt-enable update from
  // a new set of PinConfig entries. Useful for runtime reconfiguration.
  bool ConfigurePins(const PinConfig pins[8]);

  // Blocks the calling task until the shared interrupt fires or a timeout
  // occurs. Returns ESP_OK if an interrupt was received, ESP_ERR_TIMEOUT
  // if the timeout elapsed. timeout_ms of portMAX_DELAY means wait forever.
  esp_err_t WaitForInterrupt(uint32_t timeout_ms = portMAX_DELAY);

  // ---------------------------------------------------------------------------
  // Direct register access — for low-level use or register dumps.
  // ---------------------------------------------------------------------------
  esp_err_t WriteReg(uint8_t reg, uint8_t value);
  esp_err_t ReadReg(uint8_t reg, uint8_t* value);

 private:
  esp_err_t ApplyPinConfig(const PinConfig pins[8]);

  // Linked-list node so the shared ISR can walk all live instances.
  // Protected by s_instance_mutex_.
  void RegisterInstance();
  void UnregisterInstance();

  const Config            config_;
  i2c_master_dev_handle_t i2c_handle_       = nullptr;
  i2c_master_bus_handle_t owned_bus_handle_ = nullptr;

  // Per-instance semaphore posted by the shared ISR.
  SemaphoreHandle_t int_sem_ = nullptr;

  // Singly-linked list of all initialised instances (for ISR fanout).
  Fxl6408* next_instance_ = nullptr;

  // ---- Shared statics -------------------------------------------------------
  static gpio_num_t        s_int_pin_;
  static bool              s_isr_installed_;
  static Fxl6408*          s_instance_list_;
  static SemaphoreHandle_t s_instance_mutex_;

  // Global registry: index 0 = AddrLow (0x43), index 1 = AddrHigh (0x44).
  static constexpr uint8_t kNumExpanders = 2;
  static Fxl6408*          s_registry_[kNumExpanders];

  static void IRAM_ATTR SharedIsrHandler(void* arg);
};
