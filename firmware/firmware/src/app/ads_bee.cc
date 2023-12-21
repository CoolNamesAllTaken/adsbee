#include "ads_bee.hh"

#include <stdio.h> // for printing
#include "pico/stdlib.h"
#include "hardware/gpio.h"
#include "hardware/pio.h"
#include "hardware/clocks.h"
#include "hardware/pwm.h"
#include "hardware/adc.h"
// #include "hardware/dma.h"
#include "hardware/irq.h"
#include "capture.pio.h"
#include "pico/binary_info.h"
#include "hal.hh"


const uint16_t kDecodeLEDBootupNumBlinks = 4;
const uint16_t kDecodeLEDBootupBlinkPeriodMs = 200;
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

    // Figure out slice and channel values that will be used for setting PWM duty cycle.
    mtl_bias_pwm_slice_ = pwm_gpio_to_slice_num(config_.mtl_bias_pwm_pin);
    mtl_bias_pwm_chan_ = pwm_gpio_to_channel(config_.mtl_bias_pwm_pin);

}

void ADSBee::Init() {
    // Initialize the MTL bias PWM output.
    gpio_set_function(config_.mtl_bias_pwm_pin, GPIO_FUNC_PWM);
    pwm_set_wrap(mtl_bias_pwm_slice_, kMTLBiasMaxPWMCount);
    SetMTLMilliVolts(kMTLBiasDefaultMV);
    pwm_set_enabled(mtl_bias_pwm_slice_, true);

    // Initialize the ML bias ADC input.
    adc_init();
    adc_gpio_init(config_.mtl_bias_adc_pin);

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

    gpio_init(config_.status_led_pin);
    gpio_set_dir(config_.status_led_pin, GPIO_OUT);

    irq_set_exclusive_handler(preamble_detector_decode_irq, on_decode_complete);
    irq_set_enabled(preamble_detector_decode_irq, true);

    // Enable the state machines
    pio_sm_set_enabled(config_.preamble_detector_pio, preamble_detector_sm_, true);
    pio_sm_set_enabled(config_.message_decoder_pio, message_decoder_sm_, true);

    // Blink the LED a few times to indicate a successful startup.
    for (uint16_t i = 0; i < kDecodeLEDBootupNumBlinks; i++) {
        gpio_put(config_.status_led_pin, 1);
        sleep_ms(kDecodeLEDBootupBlinkPeriodMs/2);
        gpio_put(config_.status_led_pin, 0);
        sleep_ms(kDecodeLEDBootupBlinkPeriodMs/2);
    }

}

void ADSBee::Update() {
    // Turn off the decode LED if it's been on for long enough.
    if (get_time_since_boot_ms() > led_off_timestamp_ms_) {
        gpio_put(config_.status_led_pin, 0);
    }

    // Read back the MTL bias output voltage.
    adc_select_input(config_.mtl_bias_adc_input);
    mtl_bias_adc_counts_ = adc_read();

    // Update PWM output duty cycl.
    pwm_set_chan_level(mtl_bias_pwm_slice_, mtl_bias_pwm_chan_, mtl_bias_pwm_count_);

}

void ADSBee::OnDecodeComplete() {
    gpio_put(config_.status_led_pin, 1);
    led_off_timestamp_ms_ = get_time_since_boot_ms() + kDecodeLEDOnMs;

    
    uint16_t word_index = 0;
    while (!pio_sm_is_rx_fifo_empty(config_.message_decoder_pio, message_decoder_sm_)) {
        uint32_t word = pio_sm_get(config_.message_decoder_pio, message_decoder_sm_);
        printf("\t%d: %08x\r\n", word_index, word);

        switch(word_index) {
            case 0: {
                // Flush the previous word into a packet before beginning to store the new one.
                printf("New message: 0x%08x%08x%08x%04x\r\n",
                    rx_buffer_[0],
                    rx_buffer_[1],
                    rx_buffer_[2],
                    static_cast<uint16_t>((rx_buffer_[3]>>16) & 0xFFFF));
                ADSBPacket packet = ADSBPacket(rx_buffer_, ADSBPacket::kMaxPacketLenWords32);
                // printf(packet.IsValid() ? "\tVALID\r\n": "\tINVALID\r\n");
            } // intentional cascade
            case 1:
            case 2:
                rx_buffer_[word_index] = word;
                break;
            case 3:
                // Last word ingests an extra bit by accident, pinch it off here.
                // Left-align last word.
                rx_buffer_[word_index] = (word>>1)<<16;

                break;
            default:
                // Received too many bits for this to be a valid packet. Throw away extra bits!
                printf("tossing");
                pio_sm_get(config_.message_decoder_pio, message_decoder_sm_); // throw away extra bits
        }
        word_index++;
        
        
        // switch(word_index) {
        //     case 0: {
        //         // First word is the last word of the previously captured packet.
        //         // Flush the previous word into a packet before beginning to store the new one.
        //         printf("New message: 0x%08x%08x%08x%04x\r\n",
        //             rx_buffer_[0],
        //             rx_buffer_[1],
        //             rx_buffer_[2],
        //             rx_buffer_[3]>>16);
        //         ADSBPacket packet = ADSBPacket(rx_buffer_, ADSBPacket::kMaxPacketLenWords32);
        //         // printf(packet.IsValid() ? "\tVALID\r\n": "\tINVALID\r\n");
        //         break;
        //     }
        //     case 1:
        //         // printf("New message:\r\n");
        //         // printf("\t0x%08x", word);
        //         // rx_buffer_[word_index-1] = word;
        //         // break; // TODO: make this just a cascade if prints are removed
        //     case 2:
        //     case 3:
        //         // printf("%08x", word);
        //         rx_buffer_[word_index] = word;
        //         break;
        //     default:
        //         printf("tossing");
        //         pio_sm_get(config_.message_decoder_pio, message_decoder_sm_); // throw away extra bits

        // }
        // word_index++;
    }
    pio_interrupt_clear(config_.preamble_detector_pio, 0);
}

/**
 * @brief Set the Minimum Trigger Level (MTL) at the AD8314 output in milliVolts.
 * @param[in] mtl_threshold_mv Voltage level for a "high" trigger on the V_DN AD8314 output. The AD8314 has a nominal output
 * voltage of 2.25V on V_DN, with a logarithmic slope of around -42.6mV/dB and a minimum output voltage of 0.05V. Thus, power
 * levels received at the input of the AD8314 correspond to the following voltages.
 *      2250mV = -49dBm
 *      50mV = -2.6dBm
 * Note that there is a +30dB LNA gain stage in front of the AD8314, so for the overall receiver, the MTL values are
 * more like:
 *      2250mV = -79dBm
 *      50mV = -32.6dBm
 * @retval True if succeeded, False if MTL value was out of range.
*/
bool ADSBee::SetMTLMilliVolts(int mtl_threshold_mv) {
    if (mtl_threshold_mv > kMTLBiasMaxMV || mtl_threshold_mv < kMTLBiasMinMV) {
        return false;
    }

    // float mtl_mv_f = static_cast<float>(mtl_threshold_mv);
    // float mtl_bias_pwm_count_f = kMTLBiasPWMCompCoeffX3*mtl_mv_f*mtl_mv_f*mtl_mv_f
    //     + kMTLBiasPWMCompCoeffX2*mtl_mv_f*mtl_mv_f
    //     + kMTLBiasPWMCompCoeffX*mtl_mv_f
    //     + kMTLBiasPWMCompCoeffConst;
    // if (mtl_bias_pwm_count_f < 0) {
    //     mtl_bias_pwm_count_ = 0;
    // } else if (mtl_bias_pwm_count_f > kMTLBiasMaxPWMCount) {
    //     mtl_bias_pwm_count_ = kMTLBiasMaxPWMCount;
    // } else {
    //     mtl_bias_pwm_count_ = static_cast<uint16_t>(mtl_bias_pwm_count_f);
    // }

    mtl_bias_pwm_count_ = mtl_threshold_mv * kMTLBiasMaxPWMCount / kVDDMV;

    return true;
}

/**
 * @brief Return the value of the Minimum Trigger Level threshold in milliVolts.
 * @retval MTL in milliVolts.
*/
int ADSBee::GetMTLMilliVolts() {
    return mtl_bias_mv_;
}

/**
 * @brief Set the Minimum Trigger Level (MTL) at the AD8314 output in dBm.
 * @param[in] mtl_threshold_dBm Power trigger level for a "high" trigger on the AD8314 output, in dBm.
 * @retval True if succeeded, False if MTL value was out of range.
*/
bool ADSBee::SetMTLdBm(int mtl_threshold_dBm) {

    // BGA2818 is +30dBm
    return true;
}