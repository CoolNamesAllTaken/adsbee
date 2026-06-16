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

#include "led_strip.h"
#include "peripherals/ltr_329.hh"
#include "peripherals/aht20.hh"
#include "peripherals/spa06_003.hh"
#include "peripherals/mmc5603.hh"
#include "peripherals/mp2722.hh"
#include "peripherals/bq27427.hh"
#include "peripherals/fxl6408.hh"
#include "peripherals/lsm6dsv.hh"
#include "peripherals/epd/epaper_display/Display_EPD_W21_spi.hh"
#include "peripherals/epd/gui/GUI_Paint.h"


#define HARDWARE_UNIT_TESTS
// #define PRINT_HEAP_USAGE

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

void heap_caps_alloc_failed_hook(size_t requested_size, uint32_t caps, const char* function_name) {
    CONSOLE_ERROR("heap_caps_alloc_failed_hook",
                  "%s was called but failed to allocate %d bytes with 0x%lX capabilities.\r\n"
                  "\tfree heap: %d bytes\r\n"
                  "\tlargest free block: %d bytes\r\n"
                  "\tDRAM: %d bytes\r\n"
                  "\tIRAM: %d bytes\r\n",
                  function_name, requested_size, caps, heap_caps_get_free_size(MALLOC_CAP_8BIT),
                  heap_caps_get_largest_free_block(MALLOC_CAP_8BIT),
                  heap_caps_get_free_size(MALLOC_CAP_8BIT | MALLOC_CAP_INTERNAL | MALLOC_CAP_DMA),
                  heap_caps_get_free_size(MALLOC_CAP_IRAM_8BIT));
    printf("Stack trace at allocation failure:\n");
    esp_backtrace_print(20);  // Print up to 20 stack frames
}

void device_status_update_task(void* pvParameters) {
    while (1) {
        cpu_monitor.ReadCPUUsage(object_dictionary.device_status.core_0_usage_percent,
                                 object_dictionary.device_status.core_1_usage_percent);
        object_dictionary.device_status.temperature_deg_c = CPUMonitor::ReadTemperatureDegC();
        object_dictionary.device_status.heap_free_bytes = heap_caps_get_free_size(MALLOC_CAP_8BIT);
        object_dictionary.device_status.heap_largest_free_block_bytes =
            heap_caps_get_largest_free_block(MALLOC_CAP_8BIT);

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

    
    // ---- 1. Install GPIO ISR service -----------------------------------------
    

    // ---- 4. Build per-driver Config structs (GPIO expanders) --------------------
    Fxl6408::Config gpio_a_cfg;
    gpio_a_cfg.i2c_address = Fxl6408::kI2cAddressAddrLow;

    Fxl6408::Config gpio_b_cfg;
    gpio_b_cfg.i2c_address = Fxl6408::kI2cAddressAddrHigh;

    Fxl6408 gpio_a(gpio_a_cfg);
    Fxl6408 gpio_b(gpio_b_cfg);

    // Pulse the shared reset line before initialising either expander
    ESP_ERROR_CHECK(gpio_install_isr_service(0));
    if (!Fxl6408::HardwareReset()) { ESP_LOGE("app_main", "GPIO expander hardware reset failed"); }
    if (!gpio_a.Init()) { ESP_LOGE("app_main", "FXL6408 A init failed"); }
    if (!gpio_b.Init()) { ESP_LOGE("app_main", "FXL6408 B init failed"); }

    // ---- 5. Instantiate and init I2C drivers ---------------------------------
    Ltr329   ltr;
    Aht20    aht;
    Spl06003 spl;
    Mmc5603 mmc;
    Mp2722 mp;
    Bq27427 bq;
    Lsm6dsv imu;
    DisplayEpdW21 epd;

    if (!ltr.Init()) { ESP_LOGE("app_main", "LTR-329 init failed"); }
    if (!aht.Init()) { ESP_LOGE("app_main", "AHT20 init failed"); }
    if (!spl.Init()) { ESP_LOGE("app_main", "SPL06-003 init failed"); }
    if (!mmc.Init()) { ESP_LOGE("app_main", "MMC5603 init failed"); }
    if (!mp.Init()) { ESP_LOGE("app_main", "MP2722 init failed"); }
    if (!bq.Init()) { ESP_LOGE("app_main", "BQ27427 init failed"); }
    if (!imu.Init(true)) { ESP_LOGE("app_main", "LSM6DSV init failed"); }
    if (!epd.Init()) { ESP_LOGE("app_main", "EPD init failed"); }

    // ---- 8. EPD canvas setup (animated in the main loop below) ---------------
    // The bouncing-circle demo is driven from the polling loop via non-blocking
    // fast refresh; no DeepSleep here (the panel must stay awake for back-to-back
    // fast updates).
    static uint8_t epd_fb[DisplayEpdW21::kWidth / 8 * DisplayEpdW21::kHeight];
    Paint_NewImage(epd_fb, DisplayEpdW21::kWidth, DisplayEpdW21::kHeight, ROTATE_270, WHITE);
    // Display() streams the framebuffer in send-order (no per-byte vertical flip),
    // so the GUI needs no compensating mirror. If the panel comes out flipped,
    // switch to MIRROR_VERTICAL / MIRROR_HORIZONTAL (verify on hardware).
    Paint_SetMirroring(MIRROR_NONE);
    Paint_Clear(WHITE);
    epd.SetFrontLight(0.2);

    // ---- 7. Polling loop at ~30 Hz -------------------------------------------
    uint32_t sample_accumulator = 0;
    uint32_t current_sps        = 0;
    int64_t  last_sps_update    = esp_timer_get_time();
    int64_t  last_log_us        = 0;


    /// LED strip common configuration
    led_strip_config_t strip_config = {
        .strip_gpio_num = 45,  // The GPIO that connected to the LED strip's data line
        .max_leds = 9,                 // The number of LEDs in the strip,
        .led_model = LED_MODEL_WS2812, // LED strip model, it determines the bit timing
        .color_component_format = LED_STRIP_COLOR_COMPONENT_FMT_GRB, // The color component format is G-R-B
        .flags = {
            .invert_out = false, // don't invert the output signal
        }
    };

    /// RMT backend specific configuration
    led_strip_rmt_config_t rmt_config = {
        .clk_src = RMT_CLK_SRC_DEFAULT,    // different clock source can lead to different power consumption
        .resolution_hz = 10 * 1000 * 1000, // RMT counter clock frequency: 10MHz
        .mem_block_symbols = 64,           // the memory size of each RMT channel, in words (4 bytes)
        .flags = {
            .with_dma = false, // DMA feature is available on chips like ESP32-S3/P4
        }
    };

    /// Create the LED strip object
    led_strip_handle_t led_strip = NULL;
    ESP_ERROR_CHECK(led_strip_new_rmt_device(&strip_config, &rmt_config, &led_strip));



#ifdef PRINT_HEAP_USAGE
    uint32_t last_heap_print_timestamp_ms = 0;
#endif
    while (1) {
        adsbee_server.Update();

        static uint8_t hue_offset = 0;
        static uint8_t tick = 0;
        const uint8_t brightness = 16;
        for (int i = 0; i < 9; i++) {
            uint8_t h = hue_offset + i * 28, hi = h / 43, f = (h % 43) * 6, q = 255 - f;
            uint8_t r = (uint8_t[]){255,q,0,0,f,255}[hi] * brightness / 255;
            uint8_t g = (uint8_t[]){f,255,255,q,0,0}[hi] * brightness / 255;
            uint8_t b = (uint8_t[]){0,0,f,255,255,q}[hi] * brightness / 255;
            led_strip_set_pixel(led_strip, i, r, g, b);
        }
        led_strip_refresh(led_strip);
        if (++tick >= 20) { hue_offset += 3; tick = 0; }

        ltr.Update();
        aht.Update();
        spl.Update();
        mmc.Update();
        mp.Update();
        bq.Update();

        // Read GPIO expanders when either has a pending interrupt.
        // Replace with task-based WaitForInterrupt() for lower latency.
        uint8_t gpio_a_inputs = 0, gpio_b_inputs = 0;
        gpio_a.ReadInputs(&gpio_a_inputs);
        gpio_b.ReadInputs(&gpio_b_inputs);

        // The IMU reader task handles quaternion updates asynchronously via INT2.

        sample_accumulator++;

        int64_t now = esp_timer_get_time();
        if (now - last_sps_update >= 1000000) {
            current_sps        = sample_accumulator;
            sample_accumulator = 0;
            last_sps_update    = now;
        }

        if (now - last_log_us >= 500000) {  // 500 000 µs = 2 Hz
            last_log_us = now;
            ESP_LOGI("app_main",
                    "SPS:%3u | "
                    "L:%7.2f c0:%5u c1:%5u | "
                    "T_a:%5.2fC H:%5.2f%% | "
                    "P:%8.2f T_s:%5.2fC A:%7.2fm | "
                    "Mx:%7.2f My:%7.2f Mz:%7.2f uT T_m:%5.2fC | "
                    "PG:%d | "
                    "SOC:%s%u%% Pwr:%s%dmW | "
                    "Q:%s w:%6.3f x:%6.3f y:%6.3f z:%6.3f",
                    current_sps,
                    ltr.GetLux(), ltr.GetCh0Raw(), ltr.GetCh1Raw(),
                    aht.GetTemperatureCelsius(), aht.GetRelativeHumidity(),
                    spl.GetPressureHpa(), spl.GetTemperatureCelsius(),
                    spl.GetAltitudeMeters(),
                    mmc.GetMagneticFieldXUt(),
                    mmc.GetMagneticFieldYUt(),
                    mmc.GetMagneticFieldZUt(),
                    mmc.GetTemperatureCelsius(),
                    mp.IsPowerGood() ? 1 : 0,
                    bq.IsDataValid() ? "" : "?",
                    bq.GetStateOfChargePct(),
                    bq.IsDataValid() ? "" : "?",
                    bq.GetAveragePowerMw(),
                    imu.IsQuaternionValid() ? "ok" : "--",
                    imu.GetQuaternion().w, imu.GetQuaternion().x,
                    imu.GetQuaternion().y, imu.GetQuaternion().z);
        }

        // Bouncing circle on the EPD via non-blocking partial refresh. A new
        // frame is only drawn/pushed once the previous partial update finishes,
        // so the animation runs sub-second per step while this loop keeps
        // spinning at ~30 Hz. DisplayFast() does a differential (no-flash) update;
        // the first call stages the base image. Some ghosting accumulates over
        // time — drop a periodic epd.Display(epd_fb) in here to clear it.
        {
            static constexpr int kCanvasW = DisplayEpdW21::kHeight;  // 264 (ROTATE_270)
            static constexpr int kCanvasH = DisplayEpdW21::kWidth;   // 176
            static constexpr int kBallR   = 20;
            static int ball_x  = kBallR;
            static int ball_y  = kBallR;
            static int ball_vx = 6;
            static int ball_vy = 4;
            if (!epd.IsBusy()) {
                ball_x += ball_vx;
                ball_y += ball_vy;
                if (ball_x <= kBallR || ball_x >= kCanvasW - kBallR) ball_vx = -ball_vx;
                if (ball_y <= kBallR || ball_y >= kCanvasH - kBallR) ball_vy = -ball_vy;
                // Clamp so a large step near a wall can't escape on one frame.
                if (ball_x < kBallR) ball_x = kBallR;
                if (ball_x > kCanvasW - kBallR) ball_x = kCanvasW - kBallR;
                if (ball_y < kBallR) ball_y = kBallR;
                if (ball_y > kCanvasH - kBallR) ball_y = kCanvasH - kBallR;
                Paint_Clear(WHITE);
                Paint_DrawCircle(ball_x, ball_y, kBallR, BLACK, DRAW_FILL_FULL, DOT_PIXEL_1X1);
                epd.DisplayFast(epd_fb);  // returns immediately
            }
        }

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