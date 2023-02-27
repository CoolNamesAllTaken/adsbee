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
    PIO capture_pio = pio1;
    static const uint pulses_pin = 19; // Reading ADS-B on GPIO22. Will look for DECODE signal on GPIO22-1 = GPIO21.
    static const uint decode_in_pin = pulses_pin+1;
    static const uint decode_out_pin = 21; // Use GPIO20 as DECODE signal output, will be wired to GPIO21 as input.

    static const float preamble_detector_freq = 16e6; // Running at 16MHz (8 clock cycles per half bit).
    // Calculate the PIO clock divider.
    float preamble_detector_div = (float)clock_get_hz(clk_sys) / preamble_detector_freq;

    // Get first free state machine in capture_pio.
    uint preamble_detector_sm = pio_claim_unused_sm(capture_pio, true);
    // Add PIO program to PIO instruction memory. SDK will find location and return
    // with the memory offset of the program.
    uint preamble_detector_offset = pio_add_program(capture_pio, &preamble_detector_program);

    // Initialize the program using the .pio file helper function
    preamble_detector_program_init(
        capture_pio, preamble_detector_sm, preamble_detector_offset, pulses_pin,
        decode_out_pin, preamble_detector_div
    );
    pio_sm_set_enabled(capture_pio, preamble_detector_sm, true);

    uint message_decoder_sm = pio_claim_unused_sm(capture_pio, true);
    uint message_decoder_offset = pio_add_program(capture_pio, &message_decoder_program);
    float message_decoder_freq = 12e6; // Run at 12 MHz to decode bits at 1Mbps.
    float message_decoder_div = (float)clock_get_hz(clk_sys) / message_decoder_freq;
    message_decoder_program_init(
        capture_pio, message_decoder_sm, message_decoder_offset,
        pulses_pin, message_decoder_div
    );

    printf("main.cpp: PIOs initialized.\r\n");

    // Do nothing
    while (true) {
        printf("%08x\r\n", pio_sm_get_blocking(capture_pio, message_decoder_sm));
    }

    

    while (true) {

    }
}