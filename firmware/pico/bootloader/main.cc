#include "hal.hh"
#include "stdio.h"

static const uint16_t kStatusLEDPin = 15;
static const uint16_t kBlinkDurationMs = 500;
static const uint16_t kNumBlinks = 2;

void set_status_led_for_duration(bool led_on, uint16_t duration_ms) {
    gpio_put(kStatusLEDPin, led_on);
    busy_wait_ms(duration_ms);
}

int main() {
    stdio_init_all();
    // stdio_set_translate_crlf(&stdio_usb, false);

    gpio_init(kStatusLEDPin);
    gpio_set_dir(kStatusLEDPin, GPIO_OUT);
    printf("ADSBEE 1090 BOOTLOADER\r\n");
    for (uint16_t i = 0; i < kNumBlinks; i++) {
        set_status_led_for_duration(true, kBlinkDurationMs / 2);
        set_status_led_for_duration(false, kBlinkDurationMs / 2);
    }
}