#pragma once

#include "bsp.hh"
#include "hardware/spi.h"

class Si4362 {
   public:
    struct Si4362Config {
        uint32_t spi_clk_freq_hz = bsp.copro_spi_clk_freq_hz;
        spi_inst_t *spi_handle = bsp.copro_spi_handle;
        uint16_t spi_clk_pin = bsp.copro_spi_clk_pin;  // Pin for SPI clock (SCK).
        uint16_t spi_mosi_pin = bsp.copro_spi_mosi_pin;
        uint16_t spi_miso_pin = bsp.copro_spi_miso_pin;
        uint16_t spi_cs_pin = bsp.r978_cs_pin;
        gpio_drive_strength spi_drive_strength = bsp.copro_spi_drive_strength;
        bool spi_pullup = bsp.copro_spi_pullup;
        bool spi_pulldown = bsp.copro_spi_pulldown;
        uint16_t enable_pin = bsp.r978_enable_pin;  // Pin to enable the Si4362.
        uint16_t irq_pin = bsp.r978_irq_pin;        // Pin for Si4362 IRQ.
    };

    Si4362(Si4362Config config_in) : config_(config_in) {};
    ~Si4362();

    /**
     * Initialize Si4362.
     * @param[in] spi_already_initialized Set to true if using a shared SPI bus such that the SPI bus is already
     * initialized.
     */
    bool Init(bool spi_already_initialized = false);

   private:
    Si4362Config config_;
};