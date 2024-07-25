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
const float kPreambleDetectorFreq = 16e6;  // Running at 16MHz (8 clock cycles per half bit).

const uint8_t kRxGainDigipotI2CAddr = 0b0101111;  // MCP4017-104e
const uint32_t kRxgainDigipotOhmsPerCount = 100e3 / 127;

ADSBee *isr_access = nullptr;

void on_demod_complete() { isr_access->OnDemodComplete(); }

void on_systick_exception() { isr_access->OnSysTickWrap(); }

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
        CONSOLE_ERROR("ADSBee::Init: Failed to read wiper position from Rx Gain Digipot at I2C address 0x%x.",
                      kRxGainDigipotI2CAddr);
        return false;
    }

    // Enable the MLAT timer using the 24-bit SysTick timer connected to the 125MHz processor clock.
    // SysTick Control and Status Register
    systick_hw->csr = 0b110;  // Source = External Reference Clock, TickInt = Enabled, Counter = Disabled.
    // SysTick Reload Value Register
    systick_hw->rvr = 0xFFFFFF;  // Use the full 24 bit span of the timer value register.
    // 0xFFFFFF = 16777215 counts @ 125MHz = approx. 0.134 seconds.
    // Call the OnSysTickWrap function every time the SysTick timer hits 0.
    exception_set_exclusive_handler(SYSTICK_EXCEPTION, on_systick_exception);
    // Let the games begin!
    systick_hw->csr |= 0b1;  // Enable the counter.

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
    float message_demodulator_freq = 16e6;  // Run at 16 MHz to demodulate bits at 1Mbps.
    float message_demodulator_div = (float)clock_get_hz(clk_sys) / message_demodulator_freq;
    message_demodulator_program_init(config_.message_demodulator_pio, message_demodulator_sm_,
                                     message_demodulator_offset_, config_.pulses_pin, config_.recovered_clk_pin,
                                     message_demodulator_div);

    CONSOLE_INFO("ADSBee::Init: PIOs initialized.");

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

        sampled_mlat_48mhz_counts_ = GetMLAT48MHzCounts();
    }
}

void ADSBee::OnDemodComplete() {
    uint16_t word_index = 0;
    while (!pio_sm_is_rx_fifo_empty(config_.message_demodulator_pio, message_demodulator_sm_)) {
        uint32_t word = pio_sm_get(config_.message_demodulator_pio, message_demodulator_sm_);
        // CONSOLE_PRINTF("\t%d: %08x\r\n", word_index, word);

        switch (word_index) {
            case 0: {
                // Flush the previous word into a packet before beginning to store the new one.
                // First word out of the FIFO is actually the last word of the previously demodulated message.
                // Assemble a packet buffer using the items in rx_buffer_.
                uint32_t packet_buffer[DecodedTransponderPacket::kMaxPacketLenWords32];
                for (uint16_t i = 0; i < last_demod_num_words_ingested_; i++) {
                    packet_buffer[i] = rx_buffer_[i];
                }
                // Need to left-align by 16 bits for last word of 112-bit packet, 8 bits for last word of 56-bit
                // packet.
                if (last_demod_num_words_ingested_ == DecodedTransponderPacket::kExtendedSquitterPacketNumWords32 - 1) {
                    // 112-bit packet: trim off extra bit, mask to 16 bits, left align.
                    packet_buffer[last_demod_num_words_ingested_] = ((word >> 1) & 0xFFFF) << 16;
                } else {
                    // 56-bit packet: trim off extra bit, mask to 24 bits, left align.
                    packet_buffer[last_demod_num_words_ingested_] = ((word >> 1) & 0xFFFFFF) << 8;
                }
                DecodedTransponderPacket packet =
                    DecodedTransponderPacket(packet_buffer, last_demod_num_words_ingested_ + 1, GetLastMessageRSSIdBm(),
                                             GetLastMessageMLAT12MHzCounts());
                transponder_packet_queue.Push(packet);
                last_demod_num_words_ingested_ = 0;
                break;
            }
            case 1:
                // Slurp up the sampled RSSI and MLAT timer values while we know we're still aligned with the decode
                // interval.
                last_message_rssi_adc_counts_ = sampled_rssi_adc_counts_;
                last_message_mlat_48mhz_counts_ = sampled_mlat_48mhz_counts_;
            case 2:
            case 3:
                rx_buffer_[word_index - 1] = word;
                last_demod_num_words_ingested_ = word_index;
                break;
            default:
                // Received too many bits for this to be a valid packet. Throw away extra bits!
                // CONSOLE_PRINTF("tossing\r\n");
                // Throw away extra bits.
                break;
        }
        word_index++;
    }

    gpio_put(config_.rssi_clear_pin, 1);  // restore RSSI peak detector to working order.
    pio_interrupt_clear(config_.preamble_detector_pio, 0);
}

void ADSBee::OnSysTickWrap() { mlat_counter_1s_wraps_++; }

uint64_t ADSBee::GetMLAT48MHzCounts(uint16_t num_bits) {
    // Combine the wrap counter with the current value of the SysTick register and mask to 48 bits.
    // Note: 24-bit SysTick value is subtracted from UINT_24_MAX to make it count up instead of down.
    return (mlat_counter_1s_wraps_ << 24 | (0xFFFFFF - systick_hw->cvr)) & (UINT64_MAX >> (64 - num_bits));
}

uint64_t ADSBee::GetMLAT12MHzCounts(uint16_t num_bits) {
    // Piggyback off the higher resolution 48MHz timer function.
    return GetMLAT48MHzCounts(50) >> 2;  // Divide 48MHz counter by 4, widen the mask by 2 bits to compensate.
}

bool ADSBee::SetTLHiMilliVolts(int tl_hi_mv) {
    if (tl_hi_mv > kTLMaxMV || tl_hi_mv < kTLMinMV) {
        CONSOLE_PRINTF(
            "ADSBee::SetTLHiMilliVolts: Unable to set tl_hi_mv_ to %d, outside of permissible range %d-%d.\r\n",
            tl_hi_mv, kTLMinMV, kTLMaxMV);
        return false;
    }
    tl_hi_mv_ = tl_hi_mv;
    tl_hi_pwm_count_ = tl_hi_mv_ * kTLMaxPWMCount / kVDDMV;

    return true;
}

bool ADSBee::SetTLLoMilliVolts(int tl_lo_mv) {
    if (tl_lo_mv > kTLMaxMV || tl_lo_mv < kTLMinMV) {
        CONSOLE_PRINTF(
            "ADSBee::SetTLLoMilliVolts: Unable to set tl_lo_mv_ to %d, outside of permissible range %d-%d.\r\n",
            tl_lo_mv, kTLMinMV, kTLMaxMV);
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