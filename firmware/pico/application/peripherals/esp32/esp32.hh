#pragma once

#include "bsp.hh"
#include "hardware/spi.h"

class ESP32 {
   public:
    static const uint32_t kEnableBootupDelayMs = 500;

    struct ESP32Config {
        uint16_t enable_pin = bsp.esp32_enable_pin;
        spi_inst_t* spi_handle = bsp.copro_spi_handle;
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

    // No overrides for SPI begin or end transaction, since we don't do anything special.

   private:
    ESP32Config config_;
    bool enabled_ = false;
};