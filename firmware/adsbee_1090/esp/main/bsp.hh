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

    // FXL6408 expander pin assignments.
    // Expander A = ADDR low (0x43, index 0), Expander B = ADDR high (0x44, index 1).
    static constexpr fxl6408_pin_t epd_busy_pin = FXL6408_PIN(FXL6408_EXPANDER_A, 0);
    static constexpr fxl6408_pin_t epd_rst_pin  = FXL6408_PIN(FXL6408_EXPANDER_A, 1);
};

extern BSP bsp;