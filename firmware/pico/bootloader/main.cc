#include "hal.hh"
#include "stdio.h"

static const uint16_t kStatusLEDPin = 15;
static const uint16_t kBlinkDurationMs = 500;

int main() {
    stdio_init_all();
    stdio_set_translate_crlf(&stdio_usb, false);

    gpio_init(kStatusLEDPin);
    gpio_set_dir(kStatusLEDPin, GPIO_OUT);
    while (true) {
        printf("Hello!\r\n");
        gpio_put(kStatusLEDPin, 1);
        busy_wait_ms(kBlinkDurationMs / 2);
        gpio_put(kStatusLEDPin, 0);
        busy_wait_ms(kBlinkDurationMs / 2);
    }
}