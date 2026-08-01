#include "winglet_leds.hh"

#include <algorithm>
#include <cmath>

#include "esp_log.h"

static const char* kTag = "WingletLeds";

WingletLeds::~WingletLeds() {
    if (led_strip_ != nullptr) {
        led_strip_del(led_strip_);
        led_strip_ = nullptr;
    }
}

bool WingletLeds::Init() {
    if (led_strip_ != nullptr) return true;  // Already initialized.

    led_strip_config_t strip_config = {
        .strip_gpio_num = config_.data_pin,
        .max_leds = (uint32_t)(config_.button_backlight_count + config_.port_status_count),
        .led_model = LED_MODEL_WS2812,
        .color_component_format = LED_STRIP_COLOR_COMPONENT_FMT_GRB,
        .flags = {
            .invert_out = false,
        },
    };

    led_strip_rmt_config_t rmt_config = {
        .clk_src = RMT_CLK_SRC_DEFAULT,
        .resolution_hz = config_.rmt_resolution_hz,
        .mem_block_symbols = config_.rmt_mem_block_symbols,
        .flags = {
            .with_dma = config_.rmt_with_dma,
        },
    };

    esp_err_t ret = led_strip_new_rmt_device(&strip_config, &rmt_config, &led_strip_);
    if (ret != ESP_OK) {
        ESP_LOGE(kTag, "led_strip_new_rmt_device failed: %s", esp_err_to_name(ret));
        led_strip_ = nullptr;
        return false;
    }
    return true;
}

void WingletLeds::SetPixelScaled(int i, const Color& color, float brightness) {
    // Perceived-luma normalization: a WS2812 with all three channels on emits
    // far more light than one channel on, so scaling every color by the same
    // per-channel factor makes white look much brighter than a saturated color.
    // Treat `brightness` (0..1) as a target luma fraction of full white (255):
    // scale each color so its luma hits that target, clamping channels to 255.
    float luma = 0.30f * color.r + 0.59f * color.g + 0.11f * color.b;
    if (luma < 1.0f) luma = 1.0f;  // Avoid divide-by-zero for an all-off color.

    float scale = brightness * 255.0f / luma;
    auto ch = [scale](uint8_t c) -> uint32_t {
        int v = (int)lroundf(c * scale);
        return (uint32_t)std::clamp(v, 0, 255);
    };
    led_strip_set_pixel(led_strip_, i, ch(color.r), ch(color.g), ch(color.b));
}

void WingletLeds::Render(float ambient_level, const bool* port_ok, uint8_t button_bits) {
    if (led_strip_ == nullptr) return;

    ambient_level = std::clamp(ambient_level, 0.0f, 1.0f);
    float brightness = config_.min_brightness +
                       (config_.max_brightness - config_.min_brightness) * ambient_level;
    brightness = std::clamp(brightness, config_.min_brightness, config_.max_brightness);

    // Button backlights (LEDs 0..button_backlight_count-1). White when idle,
    // blue when the corresponding button is pressed. Button bit order is
    // reversed relative to the LEDs: button bit i drives LED (n-1 - i).
    const int n_btn = config_.button_backlight_count;
    for (int i = 0; i < n_btn; i++) {
        SetPixelScaled(i, config_.button_idle_color, brightness);
    }
    for (int i = 0; i < n_btn; i++) {
        if ((button_bits & (1 << i)) == 0) {  // active-low: 0 = pressed
            int led = (n_btn - 1) - i;        // reversed mapping
            SetPixelScaled(led, config_.button_press_color, brightness);
        }
    }

    // Port-status LEDs (the remaining LEDs), green when OK / orange when fault.
    for (int i = 0; i < config_.port_status_count; i++) {
        const Color& c = port_ok[i] ? config_.port_ok_color : config_.port_fault_color;
        SetPixelScaled(n_btn + i, c, brightness);
    }

    led_strip_refresh(led_strip_);
}
