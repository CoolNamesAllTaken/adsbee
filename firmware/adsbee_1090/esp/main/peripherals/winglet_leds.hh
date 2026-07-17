#pragma once

#include <cstdint>

#include "bsp.hh"
#include "driver/gpio.h"
#include "led_strip.h"

// WS2812 status-LED strip driver for the ADSBee Winglet.
//
// The strip has two logical groups laid out contiguously:
//   - Button backlights (LEDs 0..button_backlight_count-1): behind the front-
//     panel buttons. White when idle, blue when the corresponding button is
//     pressed. The button bit order is reversed relative to the LEDs (button
//     bit i drives LED (button_backlight_count-1 - i)).
//   - Port-status LEDs (the remaining port_status_count LEDs): the left-rail
//     status ports, green when OK / orange when fault, in rail order
//     (CO, GNSS, SUBG, 2.4G, 1090).
//
// Brightness is auto-scaled from a normalized ambient light level (0 = dark,
// 1 = bright, e.g. Ltr329::GetAmbientLevel()) between [min_brightness,
// max_brightness]. Colors are normalized by perceived luma before scaling so a
// white LED (all three channels) and a single-channel color land at the same
// apparent brightness for a given brightness level (see Render()).
//
// This layout, palette, and count are winglet-specific, which is why they live
// here in the driver Config rather than in the shared BSP.
class WingletLeds {
   public:
    struct Color {
        uint8_t r, g, b;
    };

    struct Config {
        gpio_num_t data_pin = bsp.status_led_data_pin;  // WS2812 data line

        int button_backlight_count = 4;  // LEDs 0-3: front-panel button backlights
        int port_status_count      = 5;  // LEDs 4-8: CO/GNSS/SUBG/2.4G/1090 status

        // Effective brightness = clamp(min + (max - min) * ambient, min, max),
        // interpreted as a perceived-luma target (see Render()).
        float min_brightness = 0.02f;  // floor so LEDs never fully turn off
        float max_brightness = 0.4f;   // ceiling — full intensity is too bright

        // Palette — full-range hues; the driver normalizes by luma, so raw
        // brightness differences between colors are equalized at render time.
        Color button_idle_color  = {255, 255, 255};  // button backlight, not pressed
        Color button_press_color = {0, 0, 255};      // button backlight, pressed
        Color port_ok_color      = {0, 255, 0};      // port status OK
        Color port_fault_color   = {255, 85, 0};     // port status fault

        // RMT backend.
        uint32_t rmt_resolution_hz = 10 * 1000 * 1000;  // 10 MHz
        uint32_t rmt_mem_block_symbols = 64;
        bool     rmt_with_dma = true;
    };

    WingletLeds() : WingletLeds(Config{}) {}
    explicit WingletLeds(const Config& config) : config_(config) {}
    ~WingletLeds();

    WingletLeds(const WingletLeds&)            = delete;
    WingletLeds& operator=(const WingletLeds&) = delete;

    // Creates the RMT-backed LED strip device. Returns true on success.
    bool Init();

    bool IsInitialized() const { return led_strip_ != nullptr; }

    // Renders one frame:
    //   - ambient_level (0..1) sets the effective brightness.
    //   - port_ok points to port_status_count booleans (OK=green, else orange).
    //   - button_bits is the raw active-low button input (0 = pressed); a
    //     pressed button lights its backlight blue instead of white.
    // No-op if not initialized.
    void Render(float ambient_level, const bool* port_ok, uint8_t button_bits);

   private:
    // Scales a full-range color to the target perceived brightness using luma
    // normalization, then writes it to LED index i.
    void SetPixelScaled(int i, const Color& color, float brightness);

    const Config config_;
    led_strip_handle_t led_strip_ = nullptr;
};
