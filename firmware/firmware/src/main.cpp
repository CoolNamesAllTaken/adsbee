#include <stdio.h>
#include "pico/stdlib.h"
#include "hardware/gpio.h"
#include "hardware/pio.h"
#include "hardware/clocks.h"
// #include "hardware/dma.h"
#include "hardware/irq.h"
#include "blink.pio.h"
#include "capture.pio.h"
#include "pico/binary_info.h"

#define LED_PIN 25

// void dma_handler() {
//     dma_hw->ints0 = 1u << dma_chan; // clear interrupt request
// }

PIO preamble_detector_pio = pio0;
uint preamble_detector_sm = pio_claim_unused_sm(preamble_detector_pio, true);
uint preamble_detector_offset = pio_add_program(preamble_detector_pio, &preamble_detector_program);

PIO message_decoder_pio = pio1;
uint message_decoder_sm = pio_claim_unused_sm(message_decoder_pio, true);
uint message_decoder_offset = pio_add_program(message_decoder_pio, &message_decoder_program);

void on_decode_complete() {
    printf("New message:\r\n");
    while (!pio_sm_is_rx_fifo_empty(message_decoder_pio, message_decoder_sm)) {
        printf("\t%08x\r\n", pio_sm_get(message_decoder_pio, message_decoder_sm));
    }
    pio_interrupt_clear(preamble_detector_pio, 0);
}

int main() {
    bi_decl(bi_program_description("ADS-Bee ADSB Receiver"));

    stdio_init_all();

    /** PREAMBLE DETECTOR PIO **/
    static const uint pulses_pin = 19; // Reading ADS-B on GPIO22. Will look for DECODE signal on GPIO22-1 = GPIO21.
    static const uint decode_in_pin = pulses_pin+1;
    static const uint decode_out_pin = 21; // Use GPIO20 as DECODE signal output, will be wired to GPIO21 as input.
    static const float preamble_detector_freq = 16e6; // Running at 16MHz (8 clock cycles per half bit).
    // Calculate the PIO clock divider.
    float preamble_detector_div = (float)clock_get_hz(clk_sys) / preamble_detector_freq;

    // Initialize the program using the .pio file helper function
    preamble_detector_program_init(
        preamble_detector_pio, preamble_detector_sm, preamble_detector_offset, pulses_pin,
        decode_out_pin, preamble_detector_div
    );
    

    // enable the DECODE interrupt on PIO0_IRQ_0
    uint preamble_detector_decode_irq = PIO0_IRQ_0;
    pio_set_irq0_source_enabled(preamble_detector_pio, pis_interrupt0, true); // state machine 0 IRQ 0

    /** MESSAGE DECODER PIO **/
    float message_decoder_freq = 12e6; // Run at 12 MHz to decode bits at 1Mbps.
    float message_decoder_div = (float)clock_get_hz(clk_sys) / message_decoder_freq;
    message_decoder_program_init(
        message_decoder_pio, message_decoder_sm, message_decoder_offset,
        pulses_pin, message_decoder_div
    );

    // // enable the MESSAGE_READY interrupt on PIO1_IRQ_0
    // uint message_decoder_message_ready_irq = PIO1_IRQ_0;
    // pio_set_irq0_source_enabled(message_decoder_pio, pis_interrupt0, true); // state machine 1 IRQ 0

    printf("main.cpp: PIOs initialized.\r\n");

    gpio_init(LED_PIN);
    gpio_set_dir(LED_PIN, GPIO_OUT);

    irq_set_exclusive_handler(preamble_detector_decode_irq, on_decode_complete);
    irq_set_enabled(preamble_detector_decode_irq, true);

    // Enable the state machines
    pio_sm_set_enabled(preamble_detector_pio, preamble_detector_sm, true);
    pio_sm_set_enabled(message_decoder_pio, message_decoder_sm, true);

    // Do nothing
    while (true) {
        gpio_put(LED_PIN, 1);
        sleep_ms(500);
        gpio_put(LED_PIN, 0);
        sleep_ms(500);
        // printf("%08x\r\n", pio_sm_get_blocking(message_decoder_pio, message_decoder_sm));
    }
}