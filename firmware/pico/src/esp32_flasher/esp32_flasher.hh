#ifndef ESP32_SERIAL_FLASHER_HH_
#define ESP32_SERIAL_FLASHER_HH_

#include "comms.hh"
#include "hal.hh"  // For system time stuff.
#include "hardware/uart.h"
#include "pico/stdlib.h"

class ESP32SerialFlasher {
   public:
    static const uint32_t kSerialFlasherResetHoldTimeMs = 100;
    static const uint32_t kSerialFlasherBootHoldTimeMs = 50;

    struct ESP32SerialFlasherConfig {
        uart_inst_t *esp32_uart_handle = uart0;
        uint16_t esp32_uart_tx_pin = 16;
        uint16_t esp32_uart_rx_pin = 17;
        uint16_t esp32_enable_pin = 14;
        uint16_t esp32_gpio0_boot_pin = 11;
        uint32_t esp32_baudrate = 115200;
        uint32_t esp32_higher_baudrate = 230400;
        bool enable_md5_check = true;  // Enable MD5 checksum check after flashing.
    };

    enum ESP32SerialFlasherStatus { kESP32FlasherOkay = 1, kESP32FlasherErrorTimeout, kESP32FlasherError };

    ESP32SerialFlasher(ESP32SerialFlasherConfig config_in) : config_(config_in){};

    bool DeInit() {
        CONSOLE_INFO("ESP32SerialFlasher::DeInit De-Initializing ESP32 firmware upgrade peripherals.");
        uart_deinit(config_.esp32_uart_handle);

        gpio_deinit(config_.esp32_uart_tx_pin);
        gpio_deinit(config_.esp32_uart_rx_pin);
        return true;
    }

    bool Init() {
        CONSOLE_INFO("ESP32SerialFlasher::Init Initializing ESP32 firmware upgrade peripherals.");
        // Initialize the UART.
        gpio_set_function(config_.esp32_uart_tx_pin, GPIO_FUNC_UART);
        gpio_set_function(config_.esp32_uart_rx_pin, GPIO_FUNC_UART);
        uart_set_translate_crlf(config_.esp32_uart_handle, false);
        uart_init(config_.esp32_uart_handle, config_.esp32_baudrate);

        // Initialize the enable and boot pins.
        gpio_init(config_.esp32_enable_pin);
        gpio_set_dir(config_.esp32_enable_pin, GPIO_OUT);
        gpio_init(config_.esp32_gpio0_boot_pin);
        gpio_set_dir(config_.esp32_gpio0_boot_pin, GPIO_OUT);
        return true;
    }

    bool FlashESP32();

    /**  Helper functions exposed to the esp32_serial_flasher functions. **/

    ESP32SerialFlasherStatus SerialWrite(const uint8_t *src, size_t len, uint32_t timeout_us) {
        uint32_t start_timestamp_us = get_time_since_boot_us();
        // Block until the UART is writeable.
        while (!uart_is_writable(config_.esp32_uart_handle)) {
            if (get_time_since_boot_us() - start_timestamp_us > timeout_us) return kESP32FlasherErrorTimeout;
        }
        // NOTE: The timeout implementation is janky and doesn't exit the uart blocking write early.
        uart_write_blocking(config_.esp32_uart_handle, src, len);
        if (get_time_since_boot_us() - start_timestamp_us > timeout_us) {
            return kESP32FlasherErrorTimeout;
        }
        return kESP32FlasherOkay;
    }

    ESP32SerialFlasherStatus SerialRead(uint8_t *dest, size_t len, uint32_t timeout_us) {
        uint32_t start_timestamp_us = get_time_since_boot_us();
        if (!uart_is_readable_within_us(config_.esp32_uart_handle, timeout_us)) {
            return kESP32FlasherErrorTimeout;
        }
        uint8_t *dest_start = dest;
        while (dest < dest_start + len && uart_is_readable(config_.esp32_uart_handle)) {
            uart_read_blocking(config_.esp32_uart_handle, dest++, 1);
            if (get_time_since_boot_us() - start_timestamp_us > timeout_us) {
                return kESP32FlasherErrorTimeout;
            }
        }
        return kESP32FlasherOkay;
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
    }

    void SetBaudRate(uint32_t baudrate) {
        config_.esp32_baudrate = baudrate;
        uart_set_baudrate(config_.esp32_uart_handle, config_.esp32_baudrate);
    }

   private:
    ESP32SerialFlasherConfig config_;
};

extern ESP32SerialFlasher esp32_flasher;

#endif /*  */