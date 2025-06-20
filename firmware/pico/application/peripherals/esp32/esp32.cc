#include "esp32.hh"

#include "hal.hh"

ESP32::ESP32(ESP32Config config_in) : config_(config_in) {}

bool ESP32::Init() {
    // ESP32 enable pin.
    gpio_init(config_.enable_pin);
    gpio_set_dir(config_.enable_pin, GPIO_OUT);
    SetEnable(true);
    // ESP32 chip select pin.
    gpio_init(config_.spi_cs_pin);
    gpio_set_dir(config_.spi_cs_pin, GPIO_OUT);
    gpio_put(config_.spi_cs_pin, 0);
    // ESP32 handshake pin.
    gpio_init(config_.spi_handshake_pin);
    gpio_set_dir(config_.spi_handshake_pin, GPIO_IN);
    gpio_set_pulls(config_.spi_handshake_pin, true,
                   false);  // Handshake pin is pulled up to not enter bootloader on startup.
    // Handshake line being pulled up results in false positive handshakes during startup, but this only happens during
    // bootup.

    // Require SPI pins to be initialized before this function is called, since they get shared.
    gpio_set_drive_strength(config_.spi_cs_pin, config_.spi_drive_strength);
    gpio_set_pulls(config_.spi_cs_pin, config_.spi_pullup, config_.spi_pulldown);  // CS pin pulls.

    // Don't add a bootup delay here, since the ESP32 needs to query for settings on startup and we don't want to block
    // that.

    return true;
};

bool ESP32::DeInit() {
    // ESP32 enable pin.
    SetEnable(false);
    return true;
};

bool ESP32::SPIGetHandshakePinLevel(bool blocking) {
    if (blocking) {
        // Make sure the ESP32 has time to lower the handshake pin after the last transaction.
        while (get_time_since_boot_us() - spi_last_transmit_timestamp_us_ < kSPIPostTransmitLockoutUs) {
        }
        // Put CS pin LO during pre-assert interval to stop ESP32 from initiating a transaction with HANDSHAKE pin.
        SPIBeginTransaction();
        // Enforce CS pre-assert interval with blocking wait.
        uint32_t pre_assert_interval_start = get_time_since_boot_us();
        while (get_time_since_boot_us() - pre_assert_interval_start < kSPIUpdateCSPreAssertIntervalUs) {
            // Assert the CS line before the ESP32 has a chance to handshake.
            if (gpio_get(config_.spi_handshake_pin)) {
                // Allowed to exit blocking early if ESP32 asserts the HANDSHAKE pin.
                return true;
            }
        }
        return false;
    } else if (get_time_since_boot_us() - spi_last_transmit_timestamp_us_ < kSPIPostTransmitLockoutUs) {
        // Don't actually read the handshake pin if it might overlap with an existing transaction, since we could
        // try reading the slave when nothing is here (slave hasn't yet had time to de-assert handshake pin).
        return false;
    }
    return gpio_get(config_.spi_handshake_pin);
}

int ESP32::SPIWriteReadBlocking(uint8_t *tx_buf, uint8_t *rx_buf, uint16_t len_bytes, bool end_transaction) {
    int bytes_written = 0;
#ifdef ON_PICO

    // Blocking check of handshake line. If we're expecting a handshake, it's OK for the line to be high. Otherwise, we
    // need to bail out to not stomp on the ESP32's incoming message.
    if (SPIGetHandshakePinLevel(true) && !expecting_handshake_) {
        return ReturnCode::kErrorHandshakeHigh;
    }

    SPIBeginTransaction();
    // Pico SDK doesn't have nice nullptr behavior for tx_buf and rx_buf, so we have to do this.
    if (tx_buf == nullptr) {
        // Transmit 0's when reading.
        bytes_written = spi_read_blocking(config_.spi_handle, 0x0, rx_buf, len_bytes);
    } else if (rx_buf == nullptr) {
        bytes_written = spi_write_blocking(config_.spi_handle, tx_buf, len_bytes);
    } else {
        bytes_written = spi_write_read_blocking(config_.spi_handle, tx_buf, rx_buf, len_bytes);
    }

    if (end_transaction) {
        SPIEndTransaction();
        // Only the last transfer chunk of the transaction is used to record the last transmission timestamp. This stops
        // transactions from getting too long as earlier chunks reset the lockout timer for later chungs, e.g. if we
        // only read one byte we don't want to wait for the timeout before conducting the rest of the transaction.
    }
    if (bytes_written < 0) {
        CONSOLE_ERROR("ESP32::SPIWriteReadBlocking", "SPI write read call returned error code 0x%x.", bytes_written);
    }
#elif defined(ON_ESP32)
    bytes_written = config_.interface.SPIWriteReadBlocking(tx_buf, rx_buf, len_bytes, end_transaction);
#endif
    return bytes_written;
}