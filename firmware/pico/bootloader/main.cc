#include "boot_utils.hh"

static const uint16_t kBlinkDurationMs = 100;
static const uint16_t kNumBlinks = 2;

int main() {
    stdio_init_all();
    // stdio_set_translate_crlf(&stdio_usb, false);

    gpio_init(kStatusLEDPin);
    gpio_set_dir(kStatusLEDPin, GPIO_OUT);
    printf("ADSBEE 1090 BOOTLOADER\r\n");
    for (uint16_t i = 0; i < kNumBlinks; i++) {
        set_status_led_for_duration(true, kBlinkDurationMs / 2);
        set_status_led_for_duration(false, kBlinkDurationMs / 2);
        // i = 0;  // loop forever
    }

    disable_interrupts();
    reset_peripherals();
    jump_to_vtor(kFlashAddrApp0);
}