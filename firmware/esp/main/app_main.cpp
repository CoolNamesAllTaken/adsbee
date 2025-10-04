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
#include "bsp.hh"
#include "comms.hh"
#include "cpu_utils.hh"
#include "driver/gpio.h"
#include "driver/spi_slave.h"
#include "esp_debug_helpers.h"  // For esp_backtrace_print
#include "esp_log.h"
#include "esp_timer.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "hardware_unit_tests.hh"
#include "pico.hh"
#include "settings.hh"
#include "spi_coprocessor.hh"
#include "task_priorities.hh"

#define HARDWARE_UNIT_TESTS
#define PRINT_HEAP_USAGE

static const uint32_t kHeapUsagePrintIntervalMs = 100;
static const uint32_t kDeviceStatusUpdateIntervalMs = 1000;

BSP bsp = BSP();
ObjectDictionary object_dictionary;
Pico pico_ll = Pico({});
SPICoprocessor pico = SPICoprocessor({.interface = pico_ll});
ADSBeeServer adsbee_server = ADSBeeServer();
SettingsManager settings_manager = SettingsManager();
CommsManager comms_manager = CommsManager({});
CPUMonitor cpu_monitor = CPUMonitor({});

void heap_caps_alloc_failed_hook(size_t requested_size, uint32_t caps, const char *function_name) {
    printf("%s was called but failed to allocate %d bytes with 0x%lX capabilities.\n", function_name, requested_size,
           caps);
    printf("Stack trace at allocation failure:\n");
    esp_backtrace_print(10);  // Print up to 10 stack frames
}

void device_status_update_task(void *pvParameters) {
    while (1) {
        cpu_monitor.ReadCPUUsage(object_dictionary.device_status.core_0_usage_percent,
                                 object_dictionary.device_status.core_1_usage_percent);
        // object_dictionary.device_status.temperature_deg_c = CPUMonitor::ReadTemperatureDegC();
        vTaskDelay(pdMS_TO_TICKS(kDeviceStatusUpdateIntervalMs));  // Delay 1 second.
    }
}

// Main application
extern "C" void app_main(void) {
    heap_caps_register_failed_alloc_callback(heap_caps_alloc_failed_hook);

    ESP_LOGI("app_main", "Beginning ADSBee Server Application.");
    ESP_LOGI("app_main", "Default task priority: %d", uxTaskPriorityGet(NULL));

    CPUMonitor::Init();
    xTaskCreate(device_status_update_task, "DeviceStatusUpdate", kDeviceStatusUpdateTaskStackSizeBytes, NULL,
                kDeviceStatusUpdateTaskPriority, NULL);
    adsbee_server.Init();

#ifdef HARDWARE_UNIT_TESTS
    RunHardwareUnitTests();
#endif

#ifdef PRINT_HEAP_USAGE
    uint32_t last_heap_print_timestamp_ms = 0;
#endif
    while (1) {
        adsbee_server.Update();

        // Yield to the idle task to avoid a watchdog trigger. Note: Delay must be >= 10ms since 100Hz tick is typical.
        vTaskDelay(1);  // Delay 1 tick (10ms).

#ifdef PRINT_HEAP_USAGE
        if (get_time_since_boot_ms() - last_heap_print_timestamp_ms > kHeapUsagePrintIntervalMs) {
            CONSOLE_INFO("heap", "Free heap: %d, largest block: %d", heap_caps_get_free_size(MALLOC_CAP_8BIT),
                         heap_caps_get_largest_free_block(MALLOC_CAP_8BIT));
            last_heap_print_timestamp_ms = get_time_since_boot_ms();
        }
#endif
    }
}
