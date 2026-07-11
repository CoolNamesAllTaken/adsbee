/* SPI Slave example, receiver (uses SPI Slave driver to communicate with sender)

   This example code is in the Public Domain (or CC0 licensed, at your option.)

   Unless required by applicable law or agreed to in writing, this
   software is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
   CONDITIONS OF ANY KIND, either express or implied.
*/
#include <math.h>
#include <variant>
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
#include "peripherals/sd_card.hh"
#include "peripherals/sensor_fusion.hh"
#include "peripherals/terrain/terrain_loader.hh"
#include "peripherals/orientation_cube.hh"
#include "peripherals/compass.hh"
#include "peripherals/epd/epaper_display/Display_EPD_W21_spi.hh"
#include "peripherals/epd/gui/GUI_Paint.h"
#include "peripherals/epd/gui/ui_data.hh"
#include "peripherals/epd/gui/ui_screens.hh"
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
            .with_dma = true, // DMA feature is available on chips like ESP32-S3/P4
        }
    };

    /// Create the LED strip object
    led_strip_handle_t led_strip = NULL;
    ESP_ERROR_CHECK(led_strip_new_rmt_device(&strip_config, &rmt_config, &led_strip));



#ifdef PRINT_HEAP_USAGE
    uint32_t last_heap_print_timestamp_ms = 0;
#endif
    // ---- Ambient-light auto-brightness tuning constants ----------------------
    // Ambient normalization (log scale) + smoothing.
    constexpr float kLuxMin       = 5.0f;     // lux at/below -> ambient level 0 (darkest)
    constexpr float kLuxMax       = 5000.0f;  // lux at/above -> ambient level 1 (brightest)
    constexpr float kEmaAlpha     = 0.01f;     // smoothing: higher = snappier
    constexpr float kLedMinBright = 0.05f;    // floor so indicator LEDs never fully off
    // Front-light "hump" curve, keyed on the normalized ambient level (0=dark, 1=bright).
    constexpr float kFlPeakLevel  = 0.45f;    // ambient level where the front light peaks
    constexpr float kFlOffLevel   = 0.75f;    // ambient level at/above which it is off
    constexpr float kFlDarkBright = 0.15f;    // dim (not full) when fully dark — eye comfort
    constexpr float kFlPeakBright = 0.6f;     // brightness at the peak

    auto clampf = [](float v, float lo, float hi) {
        return v < lo ? lo : (v > hi ? hi : v);
    };

    // ---- Status LED colors (WS2812, scaled by auto-brightness below) ---------
    struct LedColor { uint8_t r, g, b; };
    constexpr LedColor kLedWhite  = {100, 100, 100};  // plain indicator LEDs
    constexpr LedColor kLedGreen  = {0, 150, 0};      // status OK
    constexpr LedColor kLedOrange = {150, 50, 0};    // status not OK
    constexpr LedColor kLedBlue   = {0, 0, 150};      // button-press POC indicator

    // ---- UI navigation state (driven by the 4 front-panel buttons) -----------
    // Buttons are Expander B inputs, active-low: bit0=Enter/Back, bit1=Down
    // (zoom out), bit2=OK, bit3=Up (zoom in). Edge-triggered on press.
    winglet_ui::UiScreen current_screen = winglet_ui::UiScreen::kMap;
    int zoom_index = winglet_ui::kDefaultZoomIndex;
    uint8_t prev_buttons = 0xFF;  // all released (active-low)
    char zoom_label_buf[8] = "20NM";

    while (1) {
        adsbee_server.Update();

        // Refresh the light sensor first so brightness tracks the current reading.
        ltr.Update();

        // Normalize lux -> 0..1 on a log scale (floor lux so logf() is finite).
        float lux   = ltr.GetLux();
        float l     = (lux < 1.0f) ? 1.0f : lux;
        float level = (logf(l) - logf(kLuxMin)) / (logf(kLuxMax) - logf(kLuxMin));
        level = clampf(level, 0.0f, 1.0f);

        // EMA-smooth the ambient level to avoid flicker from noisy readings.
        static float ambient = level;  // seeded on the first iteration
        ambient += kEmaAlpha * (level - ambient);

        // Indicator LEDs: match ambient, with a floor so they stay visible.
        float led_scale = kLedMinBright + (1.0f - kLedMinBright) * ambient;
        uint8_t brightness = (uint8_t)lroundf(led_scale * 255.0f);

        // EPD front light: hump curve. Dim in darkness (eye comfort), rises to a
        // peak at mid ambient, then ramps back to 0 once the room lights the panel.
        float front;
        if (ambient <= kFlPeakLevel) {
            float t = clampf(ambient / kFlPeakLevel, 0.0f, 1.0f);
            front = kFlDarkBright + (kFlPeakBright - kFlDarkBright) * t;
        } else if (ambient < kFlOffLevel) {
            float t = (ambient - kFlPeakLevel) / (kFlOffLevel - kFlPeakLevel);
            front = kFlPeakBright * (1.0f - t);
        } else {
            front = 0.0f;
        }
        epd.SetFrontLight(front);

        // Status LED strip (9 WS2812s), scaled by the auto-brightness value.
        //   LEDs 0-3: white indicators.
        //   LEDs 4-8: the five left-sidebar status ports (green = OK, orange =
        //             not), in rail order: CO, GNSS, SUBG, 2.4G, 1090.
        {
            const AircraftDictionary& led_dict = adsbee_server.GetAircraftDictionary();
            const bool port_ok[5] = {
                true,  // CO: always green for now.
                object_dictionary.composite_device_status.rp2040.rx_position_available,  // GNSS fix
                led_dict.metrics.num_uat_aircraft > 0,      // SUBG: UAT aircraft detected
                comms_manager.WiFiStationHasIP() ||
                    comms_manager.WiFiAccessPointHasClients(),  // 2.4G: Wi-Fi up (STA or AP)
                led_dict.metrics.num_mode_s_aircraft > 0,   // 1090: Mode S aircraft detected
            };

            for (int i = 0; i < 9; i++) {
                LedColor c = (i < 4) ? kLedWhite : (port_ok[i - 4] ? kLedGreen : kLedOrange);
                led_strip_set_pixel(led_strip, i, c.r * brightness / 255, c.g * brightness / 255,
                                    c.b * brightness / 255);
            }

            // BUTTON INPUT POC (remove this block + kLedBlue to revert): the 4
            // buttons are the first 4 inputs (bits 0-3) of the ADDR-high expander
            // (Expander B, 0x44), active-low (0 = pressed). The button order is
            // reversed relative to the LEDs, so button bit i drives LED (3 - i).
            uint8_t btn_inputs = 0xFF;  // default: none pressed (active-low)
            gpio_b.ReadInputs(&btn_inputs);
            for (int i = 0; i < 4; i++) {
                if ((btn_inputs & (1 << i)) == 0) {  // active-low: 0 = pressed
                    int led = 3 - i;  // reversed mapping
                    led_strip_set_pixel(led_strip, led, kLedBlue.r * brightness / 255,
                                        kLedBlue.g * brightness / 255, kLedBlue.b * brightness / 255);
                }
            }

            led_strip_refresh(led_strip);
        }

        aht.Update();
        spl.Update();
        fusion.Update();  // drives mmc.Update() internally, then fuses IMU + mag
        mp.Update();
        bq.Update();
        sd.Update();  // hot-plug: mounts on insertion, unmounts on removal

        // Terrain: load overlapping map tiles on ownship/zoom change (cheap no-op
        // otherwise; loads at most one tile per call, off the render path).
        {
            const auto& rp = object_dictionary.composite_device_status.rp2040;
            terrain.Update(rp.rx_position_available, rp.rx_position.latitude_deg,
                           rp.rx_position.longitude_deg, winglet_ui::kZoomLadderNm[zoom_index]);
        }

        // Read GPIO expanders when either has a pending interrupt.
        // Replace with task-based WaitForInterrupt() for lower latency.
        uint8_t gpio_a_inputs = 0, gpio_b_inputs = 0xFF;
        gpio_a.ReadInputs(&gpio_a_inputs);
        gpio_b.ReadInputs(&gpio_b_inputs);

        // ---- Button navigation (edge-triggered on press) --------------------
        // Active-low: a press is a 1->0 transition on that bit. Fire once per press.
        {
            uint8_t pressed = (uint8_t)(prev_buttons & ~gpio_b_inputs);  // bits that went 0
            if (pressed & (1 << 3)) {  // Up -> zoom in (toward 2 NM)
                if (zoom_index > 0) zoom_index--;
            }
            if (pressed & (1 << 1)) {  // Down -> zoom out (toward 40 NM)
                if (zoom_index < winglet_ui::kNumZoomLevels - 1) zoom_index++;
            }
            if (pressed & (1 << 2)) current_screen = winglet_ui::UiScreen::kDebug;  // OK
            if (pressed & (1 << 0)) current_screen = winglet_ui::UiScreen::kMap;    // Enter/Back
            prev_buttons = gpio_b_inputs;
        }

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
                    "Mx:%7.2f My:%7.2f Mz:%7.2f uT | "
                    "PG:%d | "
                    "SOC:%s%u%% Pwr:%s%dmW | "
                    "Q:%s w:%6.3f x:%6.3f y:%6.3f z:%6.3f | "
                    "Hdg:%6.1f P:%6.1f R:%6.1f %s%s",
                    current_sps,
                    ltr.GetLux(), ltr.GetCh0Raw(), ltr.GetCh1Raw(),
                    aht.GetTemperatureCelsius(), aht.GetRelativeHumidity(),
                    spl.GetPressureHpa(), spl.GetTemperatureCelsius(),
                    spl.GetAltitudeMeters(),
                    mmc.GetMagneticFieldXUt(),
                    mmc.GetMagneticFieldYUt(),
                    mmc.GetMagneticFieldZUt(),
                    mp.IsPowerGood() ? 1 : 0,
                    bq.IsDataValid() ? "" : "?",
                    bq.GetStateOfChargePct(),
                    bq.IsDataValid() ? "" : "?",
                    bq.GetAveragePowerMw(),
                    imu.IsQuaternionValid() ? "ok" : "--",
                    imu.GetQuaternion().w, imu.GetQuaternion().x,
                    imu.GetQuaternion().y, imu.GetQuaternion().z,
                    fusion.GetHeadingDeg(), fusion.GetPitchDeg(), fusion.GetRollDeg(),
                    fusion.IsValid() ? "" : "imu?",
                    fusion.IsCalibrated() ? "" : "cal?");
        }

        // Live sensor readout on the EPD via non-blocking OTP partial refresh.
        // A new frame is only drawn/pushed once the previous update finishes, so
        // the screen refreshes at the panel's natural rate while this loop keeps
        // spinning. DisplayFast() is a differential (no-flash) update; the first
        // call stages the base image (blocking). Some ghosting accumulates over
        // time — drop a periodic epd.Display(epd_fb) in here to clear it.
        if (!epd.IsBusy()) {
            Paint_Clear(WHITE);

            // ---- Build the map screen's live data from the ADS-B dictionary,
            // receiver position, and battery gauge. Contacts are collected into
            // a static buffer sized to the dictionary's own cap (no extra cap).
            static winglet_ui::UiContact ui_contacts[AircraftDictionary::kMaxNumAircraft];
            uint16_t num_contacts = 0;
            const AircraftDictionary& dict = adsbee_server.GetAircraftDictionary();
            for (const auto& itr : dict.dict) {
                if (num_contacts >= AircraftDictionary::kMaxNumAircraft) break;
                const float* lat = nullptr;
                const float* lon = nullptr;
                float dir = 0.0f;
                bool dir_is_heading = false;
                if (const ModeSAircraft* a = std::get_if<ModeSAircraft>(&itr.second)) {
                    if (!a->HasBitFlag(ModeSAircraft::kBitFlagPositionValid)) continue;
                    lat = &a->latitude_deg;
                    lon = &a->longitude_deg;
                    dir = a->direction_deg;
                    dir_is_heading = a->HasBitFlag(ModeSAircraft::kBitFlagDirectionIsHeading);
                } else if (const UATAircraft* u = std::get_if<UATAircraft>(&itr.second)) {
                    if (!u->HasBitFlag(UATAircraft::kBitFlagPositionValid)) continue;
                    lat = &u->latitude_deg;
                    lon = &u->longitude_deg;
                    dir = u->direction_deg;
                    dir_is_heading = u->HasBitFlag(UATAircraft::kBitFlagDirectionIsHeading);
                } else {
                    continue;
                }
                ui_contacts[num_contacts++] = {*lat, *lon, dir, dir_is_heading, /*selected=*/false};
            }

            const auto& rp2040_status = object_dictionary.composite_device_status.rp2040;
            const auto& rx_position = rp2040_status.rx_position;

            // Left-rail port status strings, one per etched port: CO / GNSS /
            // SUBG / 2.4G / 1090.
            static char rail_bufs[winglet_ui::kNumRailRows][12];
            const auto& adsb_metrics = dict.metrics;
            // CO: no CO sensor wired on the ESP yet — hard-coded to 0 for now.
            snprintf(rail_bufs[0], sizeof rail_bufs[0], "0");
            // GNSS: satellites used in the current fix. The GNSS receiver lives on the Pico;
            // its sat count is forwarded to this MCU in the RP2040 metrics struct over SPI.
            snprintf(rail_bufs[1], sizeof rail_bufs[1], "%u",
                     (unsigned)adsbee_server.rp2040_aircraft_dictionary_metrics.gnss_num_satellites);
            // SUBG: aircraft tracked via the sub-GHz (UAT) receiver.
            snprintf(rail_bufs[2], sizeof rail_bufs[2], "%u",
                     (unsigned)adsb_metrics.num_uat_aircraft);
            // 2.4G: Wi-Fi link state — "UP" if connected to anything over Wi-Fi
            // in either mode: STA has an IP (joined an upstream AP), or the ESP's
            // own AP has at least one client connected.
            bool wifi_up = comms_manager.WiFiStationHasIP() || comms_manager.WiFiAccessPointHasClients();
            snprintf(rail_bufs[3], sizeof rail_bufs[3], "%s", wifi_up ? "UP" : "DN");
            // 1090: aircraft tracked via the 1090 MHz (Mode S) receiver.
            snprintf(rail_bufs[4], sizeof rail_bufs[4], "%u",
                     (unsigned)adsb_metrics.num_mode_s_aircraft);

            winglet_ui::MapScreenData map_data{};
            map_data.contacts = ui_contacts;
            map_data.num_contacts = num_contacts;
            map_data.ownship_valid = rp2040_status.rx_position_available;
            map_data.ownship_lat_deg = rx_position.latitude_deg;
            map_data.ownship_lon_deg = rx_position.longitude_deg;
            map_data.range_nm = winglet_ui::kZoomLadderNm[zoom_index];
            snprintf(zoom_label_buf, sizeof zoom_label_buf, "%dNM",
                     (int)winglet_ui::kZoomLadderNm[zoom_index]);
            map_data.zoom_label = zoom_label_buf;
            for (int i = 0; i < winglet_ui::kNumRailRows; i++) map_data.rail[i] = rail_bufs[i];
            map_data.batt_pct = bq.GetStateOfChargePct();
            map_data.batt_valid = bq.IsDataValid();
            map_data.terrain = &terrain;

            // The debug telemetry screen keeps its live sensor references.
            winglet_ui::DebugScreenSources debug_src{ltr, aht, spl, mmc, mp, bq, imu, fusion};

            // current_screen is driven by the button navigation above.
            winglet_ui::DrawCurrentScreen(current_screen, map_data, debug_src);

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