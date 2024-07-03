#include "esp32_flasher.hh"

#include "comms.hh"
#include "esp_bin/esp_firmware.h"
#include "esp_serial_flasher/esp_loader.h"
#include "esp_serial_flasher/esp_loader_io.h"
#include "esp_serial_flasher/example_common.h"

bool ESP32SerialFlasher::FlashESP32() {
    CONSOLE_INFO("ESP32SerialFlasher::FlashESP32: Beginning serial initialization.");
    Init();
    if (connect_to_target(config_.esp32_higher_baudrate) == ESP_LOADER_SUCCESS) {
        get_example_binaries(esp_loader_get_target(), &bin);

        flash_binary(bin.boot.data, bin.boot.size, bin.boot.addr);
        flash_binary(bin.part.data, bin.part.size, bin.part.addr);
        flash_binary(bin.app.data, bin.app.size, bin.app.addr);
    } else {
        CONSOLE_ERROR("ESP32SerialFlasher::FlashESP32: Serial initialization failed.");
    }

    return true;
}

#if SERIAL_FLASHER_DEBUG_TRACE
static void transfer_debug_print(const uint8_t *data, uint16_t size, bool write) {
    static bool write_prev = false;

    if (write_prev != write) {
        write_prev = write;
        CONSOLE_PRINTF("\n--- %s ---\n", write ? "WRITE" : "READ");
    }

    for (uint32_t i = 0; i < size; i++) {
        CONSOLE_PRINTF("%02x ", data[i]);
    }
}
#endif

static uint32_t s_time_end;

esp_loader_error_t loader_port_write(const uint8_t *data, uint16_t size, uint32_t timeout) {
    ESP32SerialFlasher::ESP32SerialFlasherStatus status = esp32_flasher.SerialWrite((uint8_t *)data, size, timeout);

    if (status == ESP32SerialFlasher::kESP32FlasherOkay) {
#if SERIAL_FLASHER_DEBUG_TRACE
        transfer_debug_print(data, size, true);
#endif
        return ESP_LOADER_SUCCESS;
    } else if (status == ESP32SerialFlasher::kESP32FlasherErrorTimeout) {
        return ESP_LOADER_ERROR_TIMEOUT;
    } else {
        return ESP_LOADER_ERROR_FAIL;
    }
}

esp_loader_error_t loader_port_read(uint8_t *data, uint16_t size, uint32_t timeout) {
    ESP32SerialFlasher::ESP32SerialFlasherStatus status = esp32_flasher.SerialRead((uint8_t *)data, size, timeout);

    if (status == ESP32SerialFlasher::kESP32FlasherOkay) {
#if SERIAL_FLASHER_DEBUG_TRACE
        transfer_debug_print(data, size, false);
#endif
        return ESP_LOADER_SUCCESS;
    } else if (status == ESP32SerialFlasher::kESP32FlasherErrorTimeout) {
        return ESP_LOADER_ERROR_TIMEOUT;
    } else {
        return ESP_LOADER_ERROR_FAIL;
    }
}

void loader_port_delay_ms(uint32_t ms) { busy_wait_ms(ms); }

void loader_port_start_timer(uint32_t ms) { s_time_end = get_time_since_boot_ms() + ms; }

uint32_t loader_port_remaining_time(void) {
    int32_t remaining = s_time_end - get_time_since_boot_ms();
    return (remaining > 0) ? (uint32_t)remaining : 0;
}

esp_loader_error_t loader_port_change_transmission_rate(uint32_t baudrate) {
    esp32_flasher.SetBaudRate(baudrate);
    return ESP_LOADER_SUCCESS;  // Pico doesn't have a meaningful way to fail when setting baudrate.
}

void loader_port_debug_print(const char *str) { CONSOLE_PRINTF("DEBUG: %s", str); }