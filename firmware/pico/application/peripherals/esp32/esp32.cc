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
