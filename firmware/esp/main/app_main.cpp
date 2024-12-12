/* SPI Slave example, receiver (uses SPI Slave driver to communicate with sender)

   This example code is in the Public Domain (or CC0 licensed, at your option.)

   Unless required by applicable law or agreed to in writing, this
   software is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
   CONDITIONS OF ANY KIND, either express or implied.
*/
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "adsbee_server.hh"
#include "comms.hh"
#include "driver/gpio.h"
#include "driver/spi_slave.h"
#include "esp_log.h"
#include "esp_timer.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "hardware_unit_tests.hh"
#include "settings.hh"
#include "spi_coprocessor.hh"

#define HARDWARE_UNIT_TESTS

ObjectDictionary object_dictionary;
SPICoprocessor pico = SPICoprocessor({});
ADSBeeServer adsbee_server = ADSBeeServer();
SettingsManager settings_manager = SettingsManager();
CommsManager comms_manager = CommsManager({});

// Main application
extern "C" void app_main(void) {
    ESP_LOGI("app_main", "Beginning ADSBee Server Application.");
    adsbee_server.Init();

#ifdef HARDWARE_UNIT_TESTS
    RunHardwareUnitTests();
#endif

    while (1) {
        adsbee_server.Update();

        // Yield to the idle task to avoid a watchdog trigger. Note: Delay must be >= 10ms since 100Hz tick is typical.
        vTaskDelay(1);  // Delay 1 tick (10ms).
    }
}
