#pragma once

#include "driver/gpio.h"
#include "driver/spi_slave.h"

class BSP {
   public:
    static const spi_host_device_t copro_spi_handle = SPI2_HOST;
    static const gpio_num_t copro_spi_mosi_pin = GPIO_NUM_41;
    static const gpio_num_t copro_spi_miso_pin = GPIO_NUM_42;
    static const gpio_num_t copro_spi_clk_pin = GPIO_NUM_40;
    static const gpio_num_t copro_spi_cs_pin = GPIO_NUM_39;
    static const gpio_num_t copro_spi_handshake_pin = GPIO_NUM_0;

    static const gpio_num_t network_led_pin = GPIO_NUM_5;
};

extern BSP bsp;