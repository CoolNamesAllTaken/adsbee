#ifndef ESP32_SERIAL_FLASHER_HH_
#define ESP32_SERIAL_FLASHER_HH_

#include "ads_bee.hh"
#include "comms.hh"
#include "hal.hh"  // For system time stuff.
#include "hardware/uart.h"
#include "pico/stdlib.h"
#include "unit_conversions.hh"

class ESP32SerialFlasher {
   public:
    static const uint32_t kSerialFlasherResetHoldTimeMs = 100;
    static const uint32_t kSerialFlasherBootHoldTimeMs = 50;

    struct ESP32SerialFlasherConfig {
        uart_inst_t *esp32_uart_handle = uart0;
        uint16_t esp32_uart_tx_pin = 16;
        uint16_t esp32_uart_rx_pin = 17;
        uint16_t esp32_enable_pin = 14;
        uint16_t esp32_gpio0_boot_pin = 13;
        uint32_t esp32_baudrate = 115200;         // Previously 115200
        uint32_t esp32_higher_baudrate = 921600;  // Previously 230400
        bool enable_md5_check = true;             // Enable MD5 checksum check after flashing.
    };

    enum ESP32SerialFlasherStatus { kESP32FlasherOkay = 1, kESP32FlasherErrorTimeout, kESP32FlasherError };

    ESP32SerialFlasher(ESP32SerialFlasherConfig config_in) : config_(config_in){};

    bool DeInit() {
        CONSOLE_INFO("ESP32SerialFlasher::DeInit De-Initializing ESP32 firmware upgrade peripherals.");
        uart_deinit(config_.esp32_uart_handle);

        gpio_deinit(config_.esp32_uart_tx_pin);
        gpio_deinit(config_.esp32_uart_rx_pin);

        // Re-enable receiver after update if it was previously enabled.
        ads_bee.SetReceiverEnable(receiver_was_enabled_before_update_);
        return true;
    }

    bool Init() {
        CONSOLE_INFO("ESP32SerialFlasher::Init Initializing ESP32 firmware upgrade peripherals.");
        // Initialize the UART.
        gpio_set_function(config_.esp32_uart_tx_pin, GPIO_FUNC_UART);
        gpio_set_function(config_.esp32_uart_rx_pin, GPIO_FUNC_UART);
        uart_set_translate_crlf(config_.esp32_uart_handle, false);
        uart_set_fifo_enabled(config_.esp32_uart_handle, true);
        uart_init(config_.esp32_uart_handle, config_.esp32_baudrate);
        uart_tx_wait_blocking(config_.esp32_uart_handle);  // Wait for the UART tx buffer to drain.

        // Initialize the enable and boot pins.
        gpio_init(config_.esp32_enable_pin);
        gpio_set_dir(config_.esp32_enable_pin, GPIO_OUT);
        gpio_init(config_.esp32_gpio0_boot_pin);
        gpio_set_dir(config_.esp32_gpio0_boot_pin, GPIO_OUT);

        receiver_was_enabled_before_update_ = ads_bee.ReceiverIsEnabled();
        ads_bee.SetReceiverEnable(false);  // Disable receiver to avoid interrupts during update.

        return true;
    }

    bool FlashESP32();

    /**  Helper functions exposed to the esp32_serial_flasher functions. **/

    ESP32SerialFlasherStatus SerialWrite(const uint8_t *src, size_t len, uint32_t timeout_ms) {
        uint32_t start_timestamp_ms = get_time_since_boot_ms();
        // Block until the UART is writeable.
        while (!uart_is_writable(config_.esp32_uart_handle)) {
            if (get_time_since_boot_ms() - start_timestamp_ms > timeout_ms) return kESP32FlasherErrorTimeout;
        }
        // NOTE: The timeout implementation is janky and doesn't exit the uart blocking write early.
        uart_write_blocking(config_.esp32_uart_handle, src, len);
        if (get_time_since_boot_ms() - start_timestamp_ms > timeout_ms) {
            return kESP32FlasherErrorTimeout;
        }
        return kESP32FlasherOkay;
    }

    inline bool uart_rx_not_timed_out_yet(uart_inst_t *uart_handle, uint32_t start_timestamp_ms, uint32_t timeout_ms) {
        int32_t time_remaining_ms = start_timestamp_ms + timeout_ms - get_time_since_boot_ms();
        if (time_remaining_ms < 0) return false;
        return uart_is_readable_within_us(config_.esp32_uart_handle, time_remaining_ms * kUsPerMs);
    }

    ESP32SerialFlasherStatus SerialRead(uint8_t *dest, size_t len, uint32_t timeout_ms) {
        uint64_t start_timestamp_ms = get_time_since_boot_ms();
        uint8_t *dest_start = dest;
        while (dest < dest_start + len &&
               uart_rx_not_timed_out_yet(config_.esp32_uart_handle, start_timestamp_ms, timeout_ms)) {
            uart_read_blocking(config_.esp32_uart_handle, dest++, 1);
            if (dest - dest_start == len) {
                return kESP32FlasherOkay;  // Finished reading all the characters.
            }
        }
        return kESP32FlasherErrorTimeout;
    }

    void ResetTarget() {
        gpio_put(config_.esp32_enable_pin, 0);
        busy_wait_ms(kSerialFlasherResetHoldTimeMs);
        gpio_put(config_.esp32_enable_pin, 1);
    }

    void EnterBootloader() {
        gpio_put(config_.esp32_gpio0_boot_pin, 0);
        ResetTarget();
        busy_wait_ms(kSerialFlasherBootHoldTimeMs);
        gpio_put(config_.esp32_gpio0_boot_pin, 1);
        busy_wait_ms(100);
        // Flush the rx uart.
        while (uart_is_readable_within_us(config_.esp32_uart_handle, 100)) {
            uart_getc(config_.esp32_uart_handle);
        }
    }

    void SetBaudRate(uint32_t baudrate) {
        config_.esp32_baudrate = baudrate;
        uart_set_baudrate(config_.esp32_uart_handle, config_.esp32_baudrate);
    }

   private:
    ESP32SerialFlasherConfig config_;
    bool receiver_was_enabled_before_update_;
};

extern ESP32SerialFlasher esp32_flasher;

#endif /*  */