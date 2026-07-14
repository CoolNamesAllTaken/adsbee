#pragma once

#include "driver/gpio.h"
#include "driver/i2c_master.h"
#include "driver/ledc.h"
#include "driver/spi_slave.h"
#include "peripherals/fxl6408_pin_config.hh"

class BSP {
   public:
    static const spi_host_device_t copro_spi_handle = SPI2_HOST;
    static const gpio_num_t copro_spi_mosi_pin = GPIO_NUM_41;
    static const gpio_num_t copro_spi_miso_pin = GPIO_NUM_42;
    static const gpio_num_t copro_spi_clk_pin = GPIO_NUM_40;
    static const gpio_num_t copro_spi_cs_pin = GPIO_NUM_39;
    static const gpio_num_t copro_spi_handshake_pin = GPIO_NUM_0;

    static const gpio_num_t network_led_pin = GPIO_NUM_5;

    static const i2c_port_num_t periph_i2c_port = I2C_NUM_0;
    static const gpio_num_t periph_i2c_sda_pin = GPIO_NUM_15;
    static const gpio_num_t periph_i2c_scl_pin = GPIO_NUM_16;
    static const gpio_num_t periph_i2c_expander_int_pin   = GPIO_NUM_7;
    static const gpio_num_t periph_i2c_expander_reset_pin = GPIO_NUM_3;

    static const spi_host_device_t periph_spi_handle         = SPI3_HOST;
    static const gpio_num_t        periph_spi_mosi_pin        = GPIO_NUM_14;
    static const gpio_num_t        periph_spi_miso_pin        = GPIO_NUM_13;
    static const gpio_num_t        periph_spi_clk_pin         = GPIO_NUM_17;
    static const int               periph_spi_max_transfer_sz = 6144;  // EPD framebuffer = 5808 bytes
    static const gpio_num_t        periph_spi_imu_cs_pin      = GPIO_NUM_11;
    static const gpio_num_t        periph_spi_imu_int2_pin    = GPIO_NUM_4;

    // EPD LED front light (PWM via LEDC).
    static const gpio_num_t epd_front_light_pin = GPIO_NUM_46;
    static constexpr ledc_timer_t   epd_front_light_ledc_timer   = LEDC_TIMER_0;
    static constexpr ledc_channel_t epd_front_light_ledc_channel = LEDC_CHANNEL_0;

    // WS2812 status LED strip (button backlights + port-status LEDs), driven
    // over RMT. The LED count / layout / palette live in the WingletLeds driver
    // Config, since they are winglet-specific.
    static const gpio_num_t status_led_data_pin = GPIO_NUM_45;

    // microSD card (SDMMC, 1-bit): CMD/CLK/DAT0 on native GPIOs. External
    // pull-ups are present on all lines. No power-enable (card always powered).
    static const gpio_num_t sd_cmd_pin  = GPIO_NUM_8;
    static const gpio_num_t sd_clk_pin  = GPIO_NUM_9;
    static const gpio_num_t sd_dat0_pin = GPIO_NUM_10;

    // FXL6408 expander pin assignments.
    // Expander A = ADDR low (0x43, index 0), Expander B = ADDR high (0x44, index 1).
    static constexpr fxl6408_pin_t epd_busy_pin = FXL6408_PIN(FXL6408_EXPANDER_A, 0);
    static constexpr fxl6408_pin_t epd_rst_pin  = FXL6408_PIN(FXL6408_EXPANDER_A, 1);
    // microSD card-detect: Expander A bit 7, active-low (0 = card present).
    static constexpr fxl6408_pin_t sd_cd_pin    = FXL6408_PIN(FXL6408_EXPANDER_A, 7);

    // Battery pack specs for the BQ27427 fuel gauge (used to configure it for an
    // accurate SOC estimate). Chemistry + charge voltage mirror the MP2722
    // charger's power-on defaults (4.2 V -> BQ27427 Chem B profile 1202); the
    // capacity is the actual cell.
    static constexpr uint16_t battery_design_capacity_mah  = 5000;  // actual cell capacity
    static constexpr uint16_t battery_terminate_voltage_mv = 3588;  // discharge floor (MP2722 SYS_MIN default)
    // Chemistry profile index: 0 = A (3230/4.35V), 1 = B (1202/4.2V), 2 = C (3142/4.4V).
    static constexpr uint8_t  battery_chem_profile         = 1;     // Chem B (4.2 V)

    // The 4 front-panel buttons are FXL6408 Expander B inputs, active-low:
    //   bit0 = Enter/Back, bit1 = Down (zoom out), bit2 = OK, bit3 = Up (zoom in).
};

extern BSP bsp;