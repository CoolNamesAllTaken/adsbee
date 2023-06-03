#include "ads_bee.hh"

#include <stdio.h> // for printing
#include "pico/stdlib.h"
#include "hardware/gpio.h"
#include "hardware/pio.h"
#include "hardware/clocks.h"
// #include "hardware/dma.h"
#include "hardware/irq.h"
#include "capture.pio.h"
#include "pico/binary_info.h"
#include "hal.hh"

const uint16_t kDecodeLEDBootupNumBlinks = 4;
const uint16_t kDecodeLEDBootupBlinkPeriodMs = 1000;
const uint32_t kDecodeLEDOnMs = 100;
const float kPreambleDetectorFreq = 16e6; // Running at 16MHz (8 clock cycles per half bit).

ADSBee * isr_access = NULL;

// struct IRQParams {
//     PIO message_decoder_pio = NULL;
//     uint message_decoder_sm = 0;

//     PIO preamble_detector_pio = NULL;
    
//     uint led_pin = 0;
// };
// IRQParams irq_params;

void on_decode_complete() {
    isr_access->OnDecodeComplete();
//     gpio_put(irq_access->config_.led_pin, 1);
//     printf("New message:\r\n");
//     while (!pio_sm_is_rx_fifo_empty(irq_params.message_decoder_pio, irq_params.message_decoder_sm)) {
//         printf("\t%08x\r\n", pio_sm_get(irq_params.message_decoder_pio, irq_params.message_decoder_sm));
//         // pio_sm_get(message_decoder_pio, message_decoder_sm);
//     }
//     pio_interrupt_clear(irq_params.preamble_detector_pio, 0);
}



ADSBee::ADSBee(ADSBeeConfig config_in) {
    config_ = config_in;

    preamble_detector_sm_ = pio_claim_unused_sm(config_.preamble_detector_pio, true);
    preamble_detector_offset_ = pio_add_program(config_.preamble_detector_pio, &preamble_detector_program);

    message_decoder_sm_ = pio_claim_unused_sm(config_.message_decoder_pio, true);
    message_decoder_offset_ = pio_add_program(config_.message_decoder_pio, &message_decoder_program);

    // Put IRQ parameters into the global scope for the on_decode_complete ISR.
    isr_access = this;

}

void ADSBee::Init() {
    // Calculate the PIO clock divider.
    float preamble_detector_div = (float)clock_get_hz(clk_sys) / kPreambleDetectorFreq;

    // Initialize the program using the .pio file helper function
    preamble_detector_program_init(
        config_.preamble_detector_pio, preamble_detector_sm_, preamble_detector_offset_, config_.pulses_pin,
        config_.decode_out_pin, preamble_detector_div
    );
    

    // enable the DECODE interrupt on PIO0_IRQ_0
    uint preamble_detector_decode_irq = PIO0_IRQ_0;
    pio_set_irq0_source_enabled(config_.preamble_detector_pio, pis_interrupt0, true); // state machine 0 IRQ 0

    /** MESSAGE DECODER PIO **/
    float message_decoder_freq = 16e6; // Run at 32 MHz to decode bits at 1Mbps.
    float message_decoder_div = (float)clock_get_hz(clk_sys) / message_decoder_freq;
    message_decoder_program_init(
        config_.message_decoder_pio, message_decoder_sm_, message_decoder_offset_,
        config_.pulses_pin, message_decoder_div
    );

    printf("ADSBee::Init: PIOs initialized.\r\n");

    gpio_init(config_.led_pin);
    gpio_set_dir(config_.led_pin, GPIO_OUT);

    irq_set_exclusive_handler(preamble_detector_decode_irq, on_decode_complete);
    irq_set_enabled(preamble_detector_decode_irq, true);

    // Enable the state machines
    pio_sm_set_enabled(config_.preamble_detector_pio, preamble_detector_sm_, true);
    pio_sm_set_enabled(config_.message_decoder_pio, message_decoder_sm_, true);

    // Blink the LED a few times to indicate a successful startup.
    for (uint16_t i = 0; i < kDecodeLEDBootupNumBlinks; i++) {
        gpio_put(config_.led_pin, 1);
        sleep_ms(kDecodeLEDBootupBlinkPeriodMs/2);
        gpio_put(config_.led_pin, 0);
        sleep_ms(kDecodeLEDBootupBlinkPeriodMs/2);
    }

}

void ADSBee::Update() {
    // Turn off the decode LED if it's been on for long enough.
    if (get_time_since_boot_ms() > led_off_timestamp_ms_) {
        gpio_put(config_.led_pin, 0);
    }

}

void ADSBee::OnDecodeComplete() {
    gpio_put(config_.led_pin, 1);
    led_off_timestamp_ms_ = get_time_since_boot_ms() + kDecodeLEDOnMs;

    
    uint16_t word_index = 0;
    while (!pio_sm_is_rx_fifo_empty(config_.message_decoder_pio, message_decoder_sm_)) {
        uint32_t word = pio_sm_get(config_.message_decoder_pio, message_decoder_sm_);
        printf("\t%08x\r\n", word);
        switch(word_index) {
            case 0: {
                // First word is the last word of the previously captured packet.
                rx_buffer_[3] = word<<16;
                printf("New message: 0x%08x%08x%08x%04x\r\n",
                    rx_buffer_[0],
                    rx_buffer_[1],
                    rx_buffer_[2],
                    rx_buffer_[3]>>16);
                ADSBPacket packet = ADSBPacket(rx_buffer_, ADSBPacket::kMaxPacketLenWords32);
                // printf(packet.IsValid() ? "\tVALID\r\n": "\tINVALID\r\n");
                break;
            }
            case 1:
                // printf("New message:\r\n");
                // printf("\t0x%08x", word);
                // rx_buffer_[word_index-1] = word;
                // break; // TODO: make this just a cascade if prints are removed
            case 2:
            case 3:
                // printf("%08x", word);
                rx_buffer_[word_index-1] = word;
                break;
            default:
                printf("tossing");
                pio_sm_get(config_.message_decoder_pio, message_decoder_sm_); // throw away extra bits

        }
        word_index++;
    }
    pio_interrupt_clear(config_.preamble_detector_pio, 0);
}