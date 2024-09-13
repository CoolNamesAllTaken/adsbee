#include "ads_bee.hh"

#include <hardware/structs/systick.h>
#include <stdio.h>  // for printing

#include "hardware/adc.h"
#include "hardware/clocks.h"
#include "hardware/exception.h"
#include "hardware/gpio.h"
#include "hardware/pio.h"
#include "hardware/pwm.h"
#include "pico/stdlib.h"
#include "pico/time.h"
// #include "hardware/dma.h"
#include "capture.pio.h"
#include "hal.hh"
#include "hardware/irq.h"
#include "pico/binary_info.h"

// #include <charconv>
#include <string.h>  // for strcat

#include "comms.hh"  // For debug prints.

const uint16_t kStatusLEDBootupNumBlinks = 4;
const uint16_t kStatusLEDBootupBlinkPeriodMs = 200;
constexpr float kPreambleDetectorFreq = 48e6;    // Running at 16MHz (8 clock cycles per half bit).
constexpr float kMessageDemodulatorFreq = 16e6;  // Run at 16 MHz to demodulate bits at 1Mbps.

const uint8_t kRxGainDigipotI2CAddr = 0b0101111;  // MCP4017-104e
const uint32_t kRxgainDigipotOhmsPerCount = 100e3 / 127;

ADSBee *isr_access = nullptr;

void on_demod_complete() { isr_access->OnDemodComplete(); }

void gpio_irq_isr(uint gpio, uint32_t event_mask) { isr_access->GPIOIRQISR(gpio, event_mask); }

ADSBee::ADSBee(ADSBeeConfig config_in) {
    config_ = config_in;

    preamble_detector_sm_ = pio_claim_unused_sm(config_.preamble_detector_pio, true);
    preamble_detector_offset_ = pio_add_program(config_.preamble_detector_pio, &preamble_detector_program);

    message_demodulator_sm_ = pio_claim_unused_sm(config_.message_demodulator_pio, true);
    message_demodulator_offset_ = pio_add_program(config_.message_demodulator_pio, &message_demodulator_program);

    // Put IRQ parameters into the global scope for the on_demod_complete ISR.
    isr_access = this;

    // Figure out slice and channel values that will be used for setting PWM duty cycle.
    tl_lo_pwm_slice_ = pwm_gpio_to_slice_num(config_.tl_lo_pwm_pin);
    tl_hi_pwm_slice_ = pwm_gpio_to_slice_num(config_.tl_hi_pwm_pin);
    tl_lo_pwm_chan_ = pwm_gpio_to_channel(config_.tl_lo_pwm_pin);
    tl_hi_pwm_chan_ = pwm_gpio_to_channel(config_.tl_hi_pwm_pin);
}

bool ADSBee::Init() {
    // Initialize the TL bias PWM output.
    gpio_set_function(config_.tl_lo_pwm_pin, GPIO_FUNC_PWM);
    gpio_set_function(config_.tl_hi_pwm_pin, GPIO_FUNC_PWM);
    pwm_set_wrap(tl_lo_pwm_slice_, kTLMaxPWMCount);
    pwm_set_wrap(tl_hi_pwm_slice_, kTLMaxPWMCount);  // redundant since it's the same slice

    SetTLLoMilliVolts(SettingsManager::kDefaultTLLoMV);
    SetTLHiMilliVolts(SettingsManager::kDefaultTLHiMV);
    pwm_set_enabled(tl_lo_pwm_slice_, true);
    pwm_set_enabled(tl_hi_pwm_slice_, true);  // redundant since it's the same slice

    // Initialize the ML bias ADC input.
    adc_init();
    adc_gpio_init(config_.tl_lo_adc_pin);
    adc_gpio_init(config_.tl_hi_adc_pin);
    adc_gpio_init(config_.rssi_hold_adc_pin);

    // Initialize RSSI peak detector clear pin.
    gpio_init(config_.rssi_clear_pin);
    gpio_set_dir(config_.rssi_clear_pin, GPIO_OUT);
    gpio_put(config_.rssi_clear_pin, 1);  // RSSI clear is active LO.

    // Initialize I2C for talking to the EEPROM and rx gain digipot.
    i2c_init(config_.onboard_i2c, config_.onboard_i2c_clk_freq_hz);
    gpio_set_function(config_.onboard_i2c_sda_pin, GPIO_FUNC_I2C);
    gpio_set_function(config_.onboard_i2c_scl_pin, GPIO_FUNC_I2C);
    uint8_t wiper_value_counts;
    if (i2c_read_blocking(config_.onboard_i2c, kRxGainDigipotI2CAddr, &wiper_value_counts, 1, false) != 1) {
        CONSOLE_ERROR("ADSBee::Init", "Failed to read wiper position from Rx Gain Digipot at I2C address 0x%x.",
                      kRxGainDigipotI2CAddr);
        return false;
    }

    // create ClockSource instance to start the timer
    ClockSource::instance();

    // Calculate the PIO clock divider.
    float preamble_detector_div = (float)clock_get_hz(clk_sys) / kPreambleDetectorFreq;

    // Initialize the program using the .pio file helper function
    preamble_detector_program_init(config_.preamble_detector_pio, preamble_detector_sm_, preamble_detector_offset_,
                                   config_.pulses_pin, config_.demod_out_pin, preamble_detector_div);

    // Enable the DEMOD interrupt on PIO0_IRQ_0.
    pio_set_irq0_source_enabled(config_.preamble_detector_pio, pis_interrupt0, true);  // state machine 0 IRQ 0

    uint demod_in_irq = IO_IRQ_BANK0;

    // Set GPIO interrupts to be higher priority than the DEMOD interrupt to allow RSSI measurement.
    irq_set_priority(config_.preamble_detector_demod_irq, 1);
    irq_set_priority(demod_in_irq, 0);

    // Handle GPIO interrupts.
    gpio_set_irq_enabled_with_callback(config_.demod_in_pin, GPIO_IRQ_EDGE_RISE, true, gpio_irq_isr);

    // Handle PIO0 IRQ0.
    irq_set_exclusive_handler(config_.preamble_detector_demod_irq, on_demod_complete);
    irq_set_enabled(config_.preamble_detector_demod_irq, true);

    /** MESSAGE DEMODULATOR PIO **/
    float message_demodulator_div = (float)clock_get_hz(clk_sys) / kMessageDemodulatorFreq;
    message_demodulator_program_init(config_.message_demodulator_pio, message_demodulator_sm_,
                                     message_demodulator_offset_, config_.pulses_pin, config_.recovered_clk_pin,
                                     message_demodulator_div);

    CONSOLE_INFO("ADSBee::Init", "PIOs initialized.");

    gpio_init(config_.status_led_pin);
    gpio_set_dir(config_.status_led_pin, GPIO_OUT);

    // Enable the state machines
    pio_sm_set_enabled(config_.preamble_detector_pio, preamble_detector_sm_, true);
    pio_sm_set_enabled(config_.message_demodulator_pio, message_demodulator_sm_, true);

    // Set the last dictionary update timestamp.
    last_aircraft_dictionary_update_timestamp_ms_ = get_time_since_boot_ms();

    // Blink the LED a few times to indicate a successful startup.
    for (uint16_t i = 0; i < kStatusLEDBootupNumBlinks; i++) {
        gpio_put(config_.status_led_pin, 1);
        sleep_ms(kStatusLEDBootupBlinkPeriodMs / 2);
        gpio_put(config_.status_led_pin, 0);
        sleep_ms(kStatusLEDBootupBlinkPeriodMs / 2);
    }
    return true;
}

bool ADSBee::Update() {
    uint32_t timestamp_ms = get_time_since_boot_ms();
    // Turn off the demod LED if it's been on for long enough.
    if (timestamp_ms > led_off_timestamp_ms_) {
        gpio_put(config_.status_led_pin, 0);
    }

    // Update PWM output duty cycle.
    pwm_set_chan_level(tl_lo_pwm_slice_, tl_lo_pwm_chan_, tl_lo_pwm_count_);
    pwm_set_chan_level(tl_hi_pwm_slice_, tl_hi_pwm_chan_, tl_hi_pwm_count_);

    // Prune aircraft dictionary.
    if (last_aircraft_dictionary_update_timestamp_ms_ - timestamp_ms > config_.aircraft_dictionary_update_interval_ms) {
        aircraft_dictionary.Update(timestamp_ms);
    }
    return true;
}

void ADSBee::GPIOIRQISR(uint gpio, uint32_t event_mask) {
    if (gpio == config_.demod_in_pin && event_mask == GPIO_IRQ_EDGE_RISE) {
        gpio_acknowledge_irq(config_.demod_in_pin, GPIO_IRQ_EDGE_RISE);
        // Demodulation period is beginning!
        // Read the RSSI level of the last packet.
        adc_select_input(config_.rssi_hold_adc_input);
        sampled_rssi_adc_counts_ = adc_read();
        // RSSI peak detector will automatically clear when DEMOD pin goes LO.

        sampled_mlat_48mhz_counts_ = ClockSource::instance().Get48MHzTickCount();
    }
}

void ADSBee::OnDemodComplete() {
    // uint16_t word_index = 0;
    while (!pio_sm_is_rx_fifo_empty(config_.message_demodulator_pio, message_demodulator_sm_)) {
        uint32_t word = pio_sm_get(config_.message_demodulator_pio, message_demodulator_sm_);
        if (!rx_queue_.Push(word)) {
            CONSOLE_ERROR("ADSBee::OnDemodComplete", "Receive queue overflowed.");
        }
    }
    uint32_t word;  // Scratch for enqueueing and dequeueing.

    // This while loop looks for and end of packet delimiter in the rx_queue_. If it finds it, it forms a packet and
    // pushes it onto the transponder_packet_queue for decoding in the main loop. The loop exits when it is unable to
    // find any additional complete packets in rx_queue_ (i.e. it can't find an end of packet delimiter).
    while (true) {
        // Check that the queue has at least one packet (contains an end of message delimiter word).
        uint16_t packet_num_words = 0;
        bool found_end_of_packet = false;
        for (uint16_t i = 0; i < rx_queue_.Length() && !found_end_of_packet; i++) {
            rx_queue_.Peek(word, i);
            if (word == kRxQueuePacketDelimiter) {
                packet_num_words = i;
                found_end_of_packet = true;
            }
        }
        if (!found_end_of_packet) {
            // Can't form a complete packet with the contents of the queue, bail out.
            break;
        }
        // Clamp maximum packet size to Extended Squitter (112 bits). Extra bits will be discarded.
        if (packet_num_words > DecodedTransponderPacket::kExtendedSquitterPacketNumWords32) {
            CONSOLE_WARNING("ADSBee::OnDemodComplete",
                            "Received a packet with %d 32-bit words, expected maximum of %d.", packet_num_words,
                            DecodedTransponderPacket::kExtendedSquitterPacketNumWords32);
            packet_num_words = DecodedTransponderPacket::kExtendedSquitterPacketNumWords32;
        }
        // Stuff the packet words into a buffer.
        uint32_t packet_buffer[RawTransponderPacket::kMaxPacketLenWords32];
        for (uint16_t i = 0; i < packet_num_words; i++) {
            rx_queue_.Pop(word);
            if (i == packet_num_words - 1) {
                // Trim off extra ingested bit from last word in the packet.
                packet_buffer[i] = word >> 1;
                // Mask and left align final word based on bit length.
                switch (packet_num_words) {
                    case DecodedTransponderPacket::kSquitterPacketNumWords32:
                        packet_buffer[i] = (packet_buffer[i] & 0xFFFFFF) << 8;
                    case DecodedTransponderPacket::kExtendedSquitterPacketNumWords32:
                        packet_buffer[i] = (packet_buffer[i] & 0xFFFF) << 16;
                }
            } else {
                packet_buffer[i] = word;
            }
        }
        // Turn packet buffer into a RawTransponderpacket and push it into the queue for digestion in the main loop.
        RawTransponderPacket packet = RawTransponderPacket(packet_buffer, packet_num_words, GetLastMessageRSSIdBm(),
                                                           GetLastMessageMLAT48MHzCounts());
        transponder_packet_queue.Push(packet);

        // Drain the receive queue until we've popped the end of packet delimiter.
        while (rx_queue_.Pop(word) && word != kRxQueuePacketDelimiter) {
        }
    }

    gpio_put(config_.rssi_clear_pin, 1);  // restore RSSI peak detector to working order.
    pio_interrupt_clear(config_.preamble_detector_pio, 0);
}

bool ADSBee::SetTLHiMilliVolts(int tl_hi_mv) {
    if (tl_hi_mv > kTLMaxMV || tl_hi_mv < kTLMinMV) {
        CONSOLE_ERROR("ADSBee::SetTLHiMilliVolts",
                      "Unable to set tl_hi_mv_ to %d, outside of permissible range %d-%d.\r\n", tl_hi_mv, kTLMinMV,
                      kTLMaxMV);
        return false;
    }
    tl_hi_mv_ = tl_hi_mv;
    tl_hi_pwm_count_ = tl_hi_mv_ * kTLMaxPWMCount / kVDDMV;

    return true;
}

bool ADSBee::SetTLLoMilliVolts(int tl_lo_mv) {
    if (tl_lo_mv > kTLMaxMV || tl_lo_mv < kTLMinMV) {
        CONSOLE_ERROR("ADSBee::SetTLLoMilliVolts",
                      "Unable to set tl_lo_mv_ to %d, outside of permissible range %d-%d.\r\n", tl_lo_mv, kTLMinMV,
                      kTLMaxMV);
        return false;
    }
    tl_lo_mv_ = tl_lo_mv;
    tl_lo_pwm_count_ = tl_lo_mv_ * kTLMaxPWMCount / kVDDMV;

    return true;
}

inline int adc_counts_to_mv(uint16_t adc_counts) { return 3300 * adc_counts / 0xFFF; }

int ADSBee::ReadTLHiMilliVolts() {
    // Read back the high level TL bias output voltage.
    adc_select_input(config_.tl_hi_adc_input);
    tl_hi_adc_counts_ = adc_read();
    return adc_counts_to_mv(tl_hi_adc_counts_);
}

int ADSBee::ReadTLLoMilliVolts() {
    // Read back the low level TL bias output voltage.
    adc_select_input(config_.tl_lo_adc_input);
    tl_lo_adc_counts_ = adc_read();
    return adc_counts_to_mv(tl_lo_adc_counts_);
}

bool ADSBee::SetRxGain(int rx_gain) {
    rx_gain_ = rx_gain;
    uint32_t rx_gain_digipot_resistance_ohms = (rx_gain_ - 1) * 1e3;  // Non-inverting amp with R1 = 1kOhms.
    uint8_t wiper_value_counts = (rx_gain_digipot_resistance_ohms / kRxgainDigipotOhmsPerCount);
    return i2c_write_blocking(config_.onboard_i2c, kRxGainDigipotI2CAddr, &wiper_value_counts, 1, false) == 1;
}

int ADSBee::ReadRxGain() {
    uint8_t wiper_value_counts;
    i2c_read_blocking(config_.onboard_i2c, kRxGainDigipotI2CAddr, &wiper_value_counts, 1, false);
    return wiper_value_counts * kRxgainDigipotOhmsPerCount / 1e3 + 1;  // Non-inverting amp with R1 = 1kOhms.
}

void ADSBee::FlashStatusLED(uint32_t led_on_ms) {
    gpio_put(config_.status_led_pin, 1);
    led_off_timestamp_ms_ = get_time_since_boot_ms() + kStatusLEDOnMs;
}