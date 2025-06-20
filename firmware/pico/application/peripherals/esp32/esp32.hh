#pragma once

#include "bsp.hh"
#include "hardware/spi.h"
#include "spi_coprocessor.hh"

class ESP32 : public SPICoprocessorSlaveInterface {
   public:
    struct ESP32Config {
        uint16_t enable_pin = bsp.esp32_enable_pin;
        spi_inst_t *spi_handle = bsp.copro_spi_handle;
        uint16_t spi_cs_pin = bsp.esp32_spi_cs_pin;
        uint16_t spi_handshake_pin = bsp.esp32_spi_handshake_pin;
        gpio_drive_strength spi_drive_strength = bsp.copro_spi_drive_strength;
        bool spi_pullup = bsp.copro_spi_pullup;
        bool spi_pulldown = bsp.copro_spi_pulldown;
    };

    ESP32(ESP32Config config_in);

    bool Init();
    bool DeInit();

    inline bool IsEnabled() { return enabled_; }
    inline void SetEnable(bool enabled) {
        gpio_put(config_.enable_pin, enabled);
        enabled_ = enabled;
    }

    inline bool SPIBeginTransaction() {
        gpio_put(config_.spi_cs_pin, 0);
        return true;
    }

    inline void SPIEndTransaction() {
        expecting_handshake_ = false;  // Reset the handshake expectation after a transaction.
        gpio_put(config_.spi_cs_pin, 1);
        spi_last_transmit_timestamp_us_ = get_time_since_boot_us();
    }

    inline bool SPIClaimNextTransaction() {
        return true;  // Not multi-threaded, no need for this.
    }
    inline void SPIReleaseNextTransaction() {
        // Not multi-threaded, no need for this.
    }

    bool SPIGetHandshakePinLevel(bool blocking = true);

    int SPIWriteReadBlocking(uint8_t *tx_buf, uint8_t *rx_buf, uint16_t len_bytes = kSPITransactionMaxLenBytes,
                             bool end_transaction = true);

    // No overrides for SPI begin or end transaction, since we don't do anything special.

   private:
    ESP32Config config_;
    bool enabled_ = false;
    uint64_t spi_last_transmit_timestamp_us_ = 0;  // Timestamp of the end of the last SPI transaction.
};