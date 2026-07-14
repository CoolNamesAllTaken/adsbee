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

#include "peripherals/ltr_329.hh"
#include "peripherals/aht20.hh"
#include "peripherals/spa06_003.hh"
#include "peripherals/mmc5603.hh"
#include "peripherals/mp2722.hh"
#include "peripherals/bq27427.hh"
#include "peripherals/fxl6408.hh"
#include "peripherals/lsm6dsv.hh"
#include "peripherals/sd_card.hh"
#include "peripherals/sensor_fusion.hh"
#include "peripherals/winglet_leds.hh"
#include "peripherals/terrain/terrain_loader.hh"
#include "peripherals/epd/epaper_display/Display_EPD_W21_spi.hh"
#include "peripherals/epd/gui/GUI_Paint.h"
#include "peripherals/epd/gui/screens/screen_manager.hh"
#include "aircraft_dictionary.hh"


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

// Prints a one-line dump of every winglet sensor's latest reading. Called at
// ~2 Hz from the polling loop for bring-up visibility.
static void LogSensorReadout(uint32_t sps, const Ltr329& ltr, const Aht20& aht, const Spl06003& spl,
                             const Mmc5603& mmc, const Mp2722& mp, const Bq27427& bq,
                             const Lsm6dsv& imu, const SensorFusion& fusion) {
    ESP_LOGI("app_main",
             "SPS:%3u | "
             "L:%7.2f c0:%5u c1:%5u | "
             "T_a:%5.2fC H:%5.2f%% | "
             "P:%8.2f T_s:%5.2fC A:%7.2fm | "
             "Mx:%7.2f My:%7.2f Mz:%7.2f uT | "
             "PG:%d | "
             "SOC:%s%u%% Pwr:%s%dmW | "
             "Q:%s w:%6.3f x:%6.3f y:%6.3f z:%6.3f | "
             "Hdg:%6.1f P:%6.1f R:%6.1f %s%s",
             sps, ltr.GetLux(), ltr.GetCh0Raw(), ltr.GetCh1Raw(), aht.GetTemperatureCelsius(),
             aht.GetRelativeHumidity(), spl.GetPressureHpa(), spl.GetTemperatureCelsius(),
             spl.GetAltitudeMeters(), mmc.GetMagneticFieldXUt(), mmc.GetMagneticFieldYUt(),
             mmc.GetMagneticFieldZUt(), mp.IsPowerGood() ? 1 : 0, bq.IsDataValid() ? "" : "?",
             bq.GetStateOfChargePct(), bq.IsDataValid() ? "" : "?", bq.GetAveragePowerMw(),
             imu.IsQuaternionValid() ? "ok" : "--", imu.GetQuaternion().w, imu.GetQuaternion().x,
             imu.GetQuaternion().y, imu.GetQuaternion().z, fusion.GetHeadingDeg(),
             fusion.GetPitchDeg(), fusion.GetRollDeg(), fusion.IsValid() ? "" : "imu?",
             fusion.IsCalibrated() ? "" : "cal?");
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

    // ---- Build per-driver Config structs (GPIO expanders) -------------------
    Fxl6408::Config gpio_a_cfg;
    gpio_a_cfg.i2c_address = Fxl6408::kI2cAddressAddrLow;

    Fxl6408::Config gpio_b_cfg;
    gpio_b_cfg.i2c_address = Fxl6408::kI2cAddressAddrHigh;
    // Buttons: Expander B bits 0-3 are the 4 buttons, active-low. Configure them
    // as inputs with internal pull-ups so an unpressed button reads high.
    for (int i = 0; i < 4; i++) {
        gpio_b_cfg.pins[i].direction = Fxl6408::Direction::kInput;
        gpio_b_cfg.pins[i].pull = Fxl6408::PullMode::kPullUp;
    }

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

    // microSD (SDMMC 1-bit). Init succeeds even with no card; mounting is
    // hot-plug driven from sd.Update() in the loop below. Card-detect lives on
    // FXL6408 Expander A, which is already initialized above.
    SdCard sd;
    if (!sd.Init()) { ESP_LOGE("app_main", "SD init failed"); }
#ifdef SD_CARD_SELF_TEST
    RunSdCardSelfTest(sd);
#endif

    // Terrain map tiles (loaded from /sd/tiles on ownship/zoom change; nothing
    // renders yet — Phase 3 consumes the parsed tiles). Update() is called in the
    // loop below, off the render hot path.
    winglet_terrain::TerrainLoader terrain;
    terrain.Init(&sd);
#ifdef TERRAIN_SELF_TEST
    // Load + validate a known tile (Seattle: lat 47, lon -122 -> row 133, col 58).
    winglet_terrain::RunTerrainSelfTest(terrain, sd, 133, 58);
#endif

    // Sensor fusion owns the IMU + magnetometer; fusion.Update() drives the MMC
    // and merges the IMU's gravity-referenced quaternion with the magnetometer
    // into a single gravity + magnetic-north orientation. (Bench-tune the Config
    // axis/sign defaults — see sensor_fusion.hh.)
    SensorFusion fusion(imu, mmc);

    // ---- 8. EPD canvas setup (live sensor readout in the main loop below) ----
    // The sensor readout is drawn from the polling loop via non-blocking OTP
    // partial refresh; no DeepSleep here (the panel must stay awake for
    // back-to-back updates).
    static uint8_t epd_fb[DisplayEpdW21::kWidth / 8 * DisplayEpdW21::kHeight];
    Paint_NewImage(epd_fb, DisplayEpdW21::kWidth, DisplayEpdW21::kHeight, ROTATE_270, WHITE);
    // Display() streams the framebuffer in send-order (no per-byte vertical flip),
    // so the GUI needs no compensating mirror. If the panel comes out flipped,
    // switch to MIRROR_VERTICAL / MIRROR_HORIZONTAL (verify on hardware).
    Paint_SetMirroring(MIRROR_NONE);
    Paint_Clear(WHITE);
    epd.Display(epd_fb);
    // Front-light brightness is driven by the ambient-light auto-brightness logic
    // in the polling loop below.

    // WS2812 status LEDs (button backlights + port-status). Auto-brightness is
    // driven from the ambient-light level in the loop below.
    WingletLeds leds;
    if (!leds.Init()) { ESP_LOGE("app_main", "WingletLeds init failed"); }

    // Owns the UI navigation state (current screen + zoom) and per-frame screen
    // marshalling / dispatch. Buttons are Expander B inputs, active-low:
    // bit0=Enter/Back, bit1=Down (zoom out), bit2=OK, bit3=Up (zoom in).
    winglet_ui::ScreenManager screens;

    // ---- Polling loop at ~30 Hz ---------------------------------------------
    uint32_t sample_accumulator = 0;
    uint32_t current_sps        = 0;
    int64_t  last_sps_update    = esp_timer_get_time();
    int64_t  last_log_us        = 0;

#ifdef PRINT_HEAP_USAGE
    uint32_t last_heap_print_timestamp_ms = 0;
#endif

    while (1) {
        adsbee_server.Update();

        // Refresh the light sensor first so auto-brightness tracks the current
        // reading; the LTR driver computes the normalized ambient level itself.
        ltr.Update();
        float ambient = ltr.GetAmbientLevel();

        // EPD front light: driver applies the ambient "hump" auto-brightness curve.
        epd.SetFrontLightForAmbient(ambient);

        // Read the front-panel buttons (Expander B, active-low) once per loop;
        // used for both the LED backlight and the screen navigation below.
        uint8_t button_bits = 0xFF;  // default: none pressed (active-low)
        gpio_b.ReadInputs(&button_bits);

        // Status LEDs: 4 button backlights + 5 port-status LEDs. The port-status
        // states pull from app-level state (ADS-B dictionary, GNSS fix, Wi-Fi),
        // in rail order: CO, GNSS, SUBG, 2.4G, 1090.
        const AircraftDictionary& dict = adsbee_server.GetAircraftDictionary();
        const bool port_ok[5] = {
            true,  // CO: always green for now.
            object_dictionary.composite_device_status.rp2040.rx_position_available,  // GNSS fix
            dict.metrics.num_uat_aircraft > 0,      // SUBG: UAT aircraft detected
            comms_manager.WiFiStationHasIP() ||
                comms_manager.WiFiAccessPointHasClients(),  // 2.4G: Wi-Fi up (STA or AP)
            dict.metrics.num_mode_s_aircraft > 0,   // 1090: Mode S aircraft detected
        };
        leds.Render(ambient, port_ok, button_bits);

        aht.Update();
        spl.Update();
        fusion.Update();  // drives mmc.Update() internally, then fuses IMU + mag
        mp.Update();
        bq.Update();
        sd.Update();  // hot-plug: mounts on insertion, unmounts on removal

        // Screen navigation (edge-triggered on press) owns current screen + zoom.
        screens.HandleButtons(button_bits);

        // Terrain: load overlapping map tiles on ownship/zoom change (cheap no-op
        // otherwise; loads at most one tile per call, off the render path).
        const auto& rp2040_status = object_dictionary.composite_device_status.rp2040;
        terrain.Update(rp2040_status.rx_position_available, rp2040_status.rx_position.latitude_deg,
                       rp2040_status.rx_position.longitude_deg,
                       winglet_ui::kZoomLadderNm[screens.zoom_index()]);

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
            LogSensorReadout(current_sps, ltr, aht, spl, mmc, mp, bq, imu, fusion);
        }

        // Live screen readout on the EPD via non-blocking OTP partial refresh.
        // A new frame is only drawn/pushed once the previous update finishes, so
        // the screen refreshes at the panel's natural rate while this loop keeps
        // spinning. DisplayFast() is a differential (no-flash) update; the first
        // call stages the base image (blocking). Some ghosting accumulates over
        // time — drop a periodic epd.Display(epd_fb) in here to clear it.
        if (!epd.IsBusy()) {
            winglet_ui::MapDataSources map_src{
                .dict = dict,
                .ownship_valid = rp2040_status.rx_position_available,
                .ownship_lat_deg = rp2040_status.rx_position.latitude_deg,
                .ownship_lon_deg = rp2040_status.rx_position.longitude_deg,
                .gnss_num_satellites = adsbee_server.rp2040_aircraft_dictionary_metrics.gnss_num_satellites,
                .wifi_up = comms_manager.WiFiStationHasIP() || comms_manager.WiFiAccessPointHasClients(),
                .batt_pct = (uint8_t)bq.GetStateOfChargePct(),
                .batt_valid = bq.IsDataValid(),
                .terrain = &terrain,
            };
            winglet_ui::DebugScreenSources debug_src{ltr, aht, spl, mmc, mp, bq, imu, fusion};

            screens.Draw(map_src, debug_src);

            epd.DisplayFast(epd_fb);  // OTP partial, non-blocking; booster stays on
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