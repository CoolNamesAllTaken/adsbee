#include <stdio.h>
#include "pico/stdlib.h"
#include "hardware/gpio.h"
#include "hardware/pio.h"
#include "hardware/clocks.h"
#include "blink.pio.h"
#include "capture.pio.h"
#include "pico/binary_info.h"

int main() {
    bi_decl(bi_program_description("ADS-Bee ADSB Receiver"));

    stdio_init_all();

    // Blink PIO example
    static const uint led_pin = 25;
    static const float pio_freq = 2000;

    // Choose PIO instance (0 or 1)
    PIO pio = pio0;

    // Get first free state machine in PIO 0
    uint sm = pio_claim_unused_sm(pio, true);

    // Add PIO program to PIO instruction memory. SDK will find location and
    // return with the memory offset of the program.
    uint offset = pio_add_program(pio, &blink_program);

    // Calculate the PIO clock divider
    float div = (float)clock_get_hz(clk_sys) / pio_freq;

    // Initialize the program using the helper function in our .pio file
    blink_program_init(pio, sm, offset, led_pin, div);

    // Start running our PIO program in the state machine
    pio_sm_set_enabled(pio, sm, true);

    // Capture PIO
    static const uint capture_pio_in_pin = 28; // Reading ADS-B on GPIO28.
    static const uint capture_pio_out_pin = 22; // Use GPIO22 as a debug output from the PIO.
    static const float capture_pio_freq = 16e6; // Running at 16MHz (8 clock cycles per half bit).
    PIO capture_pio = pio1;
    // Get first free state machine in capture_pio.
    uint capture_pio_sm = pio_claim_unused_sm(capture_pio, true);
    // Add PIO program to PIO instruction memory. SDK will find location and return
    // with the memory offset of the program.
    uint capture_pio_offset = pio_add_program(capture_pio, &capture_program);
    // Calculate the PIO clock divider.
    float capture_pio_div = (float)clock_get_hz(clk_sys) / capture_pio_freq;
    // Initialize the program using the .pio file helper function
    capture_program_init(
        capture_pio, capture_pio_sm, capture_pio_offset, capture_pio_in_pin,
        capture_pio_out_pin, capture_pio_div
    );
    pio_sm_set_enabled(capture_pio, capture_pio_sm, true);


    // Do nothing
    while (true) {
        sleep_ms(1000);
    }

    

    while (true) {

    }
}