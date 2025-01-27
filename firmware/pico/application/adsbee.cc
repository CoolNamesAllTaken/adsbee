#include "adsbee.hh"

#include <hardware/structs/systick.h>

#include "hardware/adc.h"
#include "hardware/clocks.h"
#include "hardware/exception.h"
#include "hardware/gpio.h"
#include "hardware/pio.h"
#include "hardware/pwm.h"
#include "pico/rand.h"
#include "pico/stdlib.h"
#include "pico/time.h"
#include "stdio.h"  // for printing
// #include "hardware/dma.h"
#include "capture.pio.h"
#include "hal.hh"
#include "hardware/irq.h"
#include "packet_decoder.hh"
#include "pico/binary_info.h"
#include "spi_coprocessor.hh"

// #include <charconv>
#include <string.h>  // for strcat

#include "comms.hh"  // For debug prints.

constexpr float kPreambleDetectorFreq = 48e6;    // Running at 48MHz (24 clock cycles per half bit).
constexpr float kMessageDemodulatorFreq = 48e6;  // Run at 48 MHz to demodulate bits at 1Mbps.

constexpr float kInt16MaxRecip = 1.0f / INT16_MAX;

ADSBee *isr_access = nullptr;

/** Begin pass-through functions for public access **/
void on_systick_exception() { isr_access->OnSysTickWrap(); }

void on_demod_pin_change(uint gpio, uint32_t event_mask) {
    switch (event_mask) {
        case GPIO_IRQ_EDGE_RISE:
            isr_access->OnDemodBegin(gpio);
            break;
        case GPIO_IRQ_EDGE_FALL:
            break;
        case GPIO_IRQ_EDGE_RISE | GPIO_IRQ_EDGE_FALL:
            break;
    }
    gpio_acknowledge_irq(gpio, event_mask);
}

void on_demod_complete() { isr_access->OnDemodComplete(); }

/** End pass-through functions for public access **/

ADSBee::ADSBee(ADSBeeConfig config_in) {
    config_ = config_in;

    for (uint16_t sm_index = 0; sm_index < kNumDemodStateMachines; sm_index++) {
        preamble_detector_sm_[sm_index] = pio_claim_unused_sm(config_.preamble_detector_pio, true);
        message_demodulator_sm_[sm_index] = pio_claim_unused_sm(config_.message_demodulator_pio, true);
    }
    irq_wrapper_sm_ = pio_claim_unused_sm(config_.preamble_detector_pio, true);

    preamble_detector_offset_ = pio_add_program(config_.preamble_detector_pio, &preamble_detector_program);
    irq_wrapper_offset_ = pio_add_program(config_.preamble_detector_pio, &irq_wrapper_program);
    message_demodulator_offset_ = pio_add_program(config_.message_demodulator_pio, &message_demodulator_program);

    // Put IRQ parameters into the global scope for the on_demod_complete ISR.
    isr_access = this;

    // Figure out slice and channel values that will be used for setting PWM duty cycle.
    tl_pwm_slice_ = pwm_gpio_to_slice_num(config_.tl_pwm_pin);
    tl_pwm_chan_ = pwm_gpio_to_channel(config_.tl_pwm_pin);
}

bool ADSBee::Init() {
    gpio_init(config_.status_led_pin);
    gpio_set_dir(config_.status_led_pin, GPIO_OUT);
    gpio_put(config_.status_led_pin, 0);

    // Initialize the TL bias PWM output.
    gpio_set_function(config_.tl_pwm_pin, GPIO_FUNC_PWM);
    pwm_set_wrap(tl_pwm_slice_, kTLMaxPWMCount);

    SetTLMilliVolts(SettingsManager::Settings::kDefaultTLMV);
    pwm_set_enabled(tl_pwm_slice_, true);

    // Initialize the trigger level bias ADC input.
    adc_init();
    adc_gpio_init(config_.tl_adc_pin);
    adc_gpio_init(config_.rssi_adc_pin);

    // Initialize I2C for talking to the EEPROM and rx gain digipot.
    if (config_.onboard_i2c_requires_init) {
        i2c_init(config_.onboard_i2c, config_.onboard_i2c_clk_freq_hz);
        gpio_set_function(config_.onboard_i2c_sda_pin, GPIO_FUNC_I2C);
        gpio_set_function(config_.onboard_i2c_scl_pin, GPIO_FUNC_I2C);
    }

    // Initialize the bias tee.
    gpio_init(config_.bias_tee_enable_pin);
    gpio_put(config_.bias_tee_enable_pin, 1);  // Enable is active LO.
    gpio_set_dir(config_.bias_tee_enable_pin, GPIO_OUT);

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

    /** PREAMBLE DETECTOR PIO **/
    // Calculate the PIO clock divider.
    float preamble_detector_div = (float)clock_get_hz(clk_sys) / kPreambleDetectorFreq;
    irq_wrapper_program_init(config_.preamble_detector_pio, kNumDemodStateMachines, irq_wrapper_offset_,
                             preamble_detector_div);
    for (uint16_t sm_index = 0; sm_index < kNumDemodStateMachines; sm_index++) {
        // Only make the state machine wait to start if it's part of the round-robin group of well formed preamble
        // detectors.
        bool make_sm_wait = sm_index > 0 && sm_index < kHighPowerDemodStateMachineIndex;
        // Initialize the program using the .pio file helper function
        preamble_detector_program_init(config_.preamble_detector_pio,                     // Use PIO block 0.
                                       preamble_detector_sm_[sm_index],                   // State machines 0-2
                                       preamble_detector_offset_ /* + starting_offset*/,  // Program startin offset.
                                       config_.pulses_pins[sm_index],                     // Pulses pin (input).
                                       config_.demod_pins[sm_index],                      // Demod pin (output).
                                       preamble_detector_div,                             // Clock divisor (for 48MHz).
                                       make_sm_wait  // Whether state machine should wait for an IRQ to begin.
        );

        // Handle GPIO interrupts (for marking beginning of demod interval).
        gpio_set_irq_enabled_with_callback(config_.demod_pins[sm_index], GPIO_IRQ_EDGE_RISE /* | GPIO_IRQ_EDGE_FALL */,
                                           true, on_demod_pin_change);

        // Set the preamble sequnence into the ISR: ISR: 0b101000010100000(0)
        // Last 0 removed from preamble sequence to allow the demodulator more time to start up.
        // mov isr null ; Clear ISR.
        pio_sm_exec(config_.preamble_detector_pio, preamble_detector_sm_[sm_index], pio_encode_mov(pio_isr, pio_null));
        // Fill start of preamble pattern with different bits if the state machine is intended to sense high power
        // preambles.
        if (sm_index == kHighPowerDemodStateMachineIndex) {
            // High power preamble.
            // set x 0b111  ; ISR = 0b00000000000000000000000000000000
            pio_sm_exec(config_.preamble_detector_pio, preamble_detector_sm_[sm_index], pio_encode_set(pio_x, 0b111));
            // in x 3       ; ISR = 0b00000000000000000000000000000111
            pio_sm_exec(config_.preamble_detector_pio, preamble_detector_sm_[sm_index], pio_encode_in(pio_x, 3));
            // set x 0b101  ; ISR = 0b00000000000000000000000000000000
            pio_sm_exec(config_.preamble_detector_pio, preamble_detector_sm_[sm_index], pio_encode_set(pio_x, 0b101));
        } else {
            // Well formed preamble.
            // set x 0b101  ; ISR = 0b00000000000000000000000000000000
            pio_sm_exec(config_.preamble_detector_pio, preamble_detector_sm_[sm_index], pio_encode_set(pio_x, 0b101));
            // in x 3       ; ISR = 0b00000000000000000000000000000101
            pio_sm_exec(config_.preamble_detector_pio, preamble_detector_sm_[sm_index], pio_encode_in(pio_x, 3));
        }
        // in null 4    ; ISR = 0b00000000000000000000000001?10000
        pio_sm_exec(config_.preamble_detector_pio, preamble_detector_sm_[sm_index], pio_encode_in(pio_null, 4));
        // in x 3       ; ISR = 0b00000000000000000000001?10000101
        pio_sm_exec(config_.preamble_detector_pio, preamble_detector_sm_[sm_index], pio_encode_in(pio_x, 3));
        // in null 4    ; ISR = 0b0000000000000000001?100001010000
        // Note: this is shorter than the real tail but we need extra time for the demodulator to start up.
        pio_sm_exec(config_.preamble_detector_pio, preamble_detector_sm_[sm_index], pio_encode_in(pio_null, 4));
        // mov x null   ; Clear scratch x.
        pio_sm_exec(config_.preamble_detector_pio, preamble_detector_sm_[sm_index], pio_encode_mov(pio_x, pio_null));

        // Use this instruction to verify preamble was formed correctly (pushes ISR to RX FIFO).
        // pio_sm_exec(config_.preamble_detector_pio, preamble_detector_sm_[sm_index], pio_encode_push(false, true));
    }

    // Enable the DEMOD interrupt on PIO1_IRQ_0.
    pio_set_irq0_source_enabled(config_.preamble_detector_pio, pis_interrupt0, true);  // PIO0 state machine 0
    pio_set_irq0_source_enabled(config_.preamble_detector_pio, pis_interrupt1, true);  // PIO0 state machine 1
    pio_set_irq0_source_enabled(config_.preamble_detector_pio, pis_interrupt2, true);  // PIO0 state machine 2

    // Handle PIO0 IRQ0.
    irq_set_exclusive_handler(config_.preamble_detector_demod_complete_irq, on_demod_complete);
    irq_set_enabled(config_.preamble_detector_demod_complete_irq, true);

    /** MESSAGE DEMODULATOR PIO **/
    float message_demodulator_div = (float)clock_get_hz(clk_sys) / kMessageDemodulatorFreq;
    for (uint16_t sm_index = 0; sm_index < kNumDemodStateMachines; sm_index++) {
        message_demodulator_program_init(config_.message_demodulator_pio, message_demodulator_sm_[sm_index],
                                         message_demodulator_offset_, config_.pulses_pins[sm_index],
                                         config_.demod_pins[sm_index], config_.recovered_clk_pins[sm_index],
                                         message_demodulator_div);
    }

    // Set GPIO interrupts to be higher priority than the DEMOD interrupt to allow RSSI measurement.
    // irq_set_priority(config_.preamble_detector_demod_complete_irq, 1);
    irq_set_priority(config_.preamble_detector_demod_pin_irq, 0);

    CONSOLE_INFO("ADSBee::Init", "PIOs initialized.");

    // Set the last dictionary update timestamp.
    last_aircraft_dictionary_update_timestamp_ms_ = get_time_since_boot_ms();

    // Enable the state machines.
    pio_sm_set_enabled(config_.preamble_detector_pio, irq_wrapper_sm_, true);
    // Need to enable the demodulator SMs first, since if the preamble detector trips the IRQ but the demodulator isn't
    // enabled, we end up in a deadlock (I think, this maybe should be verified again).
    for (uint16_t sm_index = 0; sm_index < kNumDemodStateMachines; sm_index++) {
        // pio_sm_set_enabled(config_.preamble_detector_pio, preamble_detector_sm_[sm_index], true);
        pio_sm_set_enabled(config_.message_demodulator_pio, message_demodulator_sm_[sm_index], true);
    }
    // Enable round robin well formed preamble detectors.
    // NOTE: These need to be enable to allow the high power preamble detector to run, since they reset the IRQ that the
    // high power preamble detector relies on. This is a vestige of the fact that the high power preamble detector uses
    // the same PIO code that does round-robin for the well formed preamble detectors.
    for (uint16_t sm_index = 0; sm_index < kHighPowerDemodStateMachineIndex; sm_index++) {
        pio_sm_set_enabled(config_.preamble_detector_pio, preamble_detector_sm_[sm_index], true);
    }
    // Enable high power preamble detector.
    pio_sm_set_enabled(config_.preamble_detector_pio, preamble_detector_sm_[kHighPowerDemodStateMachineIndex], true);

    // Throw a fit if the watchdog caused a reboot.
    if (watchdog_caused_reboot()) {
        CONSOLE_WARNING("ADSBee::Init", "Watchdog caused reboot.");
        DisableWatchdog();
        SetStatusLED(true);
        sleep_ms(5000);
        SetStatusLED(false);
        EnableWatchdog();
    }

    return true;
}

bool ADSBee::Update() {
    uint32_t timestamp_ms = get_time_since_boot_ms();
    // Turn off the demod LED if it's been on for long enough.
    if (timestamp_ms - led_on_timestamp_ms_ > kStatusLEDOnMs) {
        gpio_put(config_.status_led_pin, 0);
    }

    // Prune aircraft dictionary. Need to do this up front so that we don't end up with a negative timestamp delta
    // caused by packets being ingested more recently than the timestamp we take at the beginning of this function.
    if (timestamp_ms - last_aircraft_dictionary_update_timestamp_ms_ > config_.aircraft_dictionary_update_interval_ms) {
        aircraft_dictionary.Update(timestamp_ms);
        if (esp32.IsEnabled()) {
            // Send fresh aircraft dictionary stats to ESPS32.
            esp32.Write(ObjectDictionary::kAddrAircraftDictionaryMetrics, aircraft_dictionary.metrics,
                        true);  // require ACK.
        }
        // Add the fresh metrics values to the pile used for TL learning.
        // If learning, add the number of valid packets received to the pile used for trigger level learning.
        if (tl_learning_temperature_mv_ > 0) {
            tl_learning_num_valid_packets_ += (aircraft_dictionary.metrics.valid_squitter_frames +
                                               aircraft_dictionary.metrics.valid_extended_squitter_frames);
        }
        last_aircraft_dictionary_update_timestamp_ms_ = timestamp_ms;
    }

    // Ingest new packets into the dictionary.
    // Raw1090Packet raw_packet;
    Decoded1090Packet decoded_packet;
    while (decoder.decoded_1090_packet_out_queue.Pop(decoded_packet) /*raw_1090_packet_queue.Pop(raw_packet)*/) {
        // if (raw_packet.buffer_len_bits == Decoded1090Packet::kExtendedSquitterPacketLenBits) {
        //     CONSOLE_INFO("ADSBee::Update", "New message: 0x%08x|%08x|%08x|%04x SRC=%d SIGS=%ddBm SIGQ=%ddB MLAT=%u",
        //                  raw_packet.buffer[0], raw_packet.buffer[1], raw_packet.buffer[2],
        //                  (raw_packet.buffer[3]) >> (4 * kBitsPerNibble), raw_packet.source, raw_packet.sigs_dbm,
        //                  raw_packet.sigq_db, raw_packet.mlat_48mhz_64bit_counts);
        // } else {
        //     CONSOLE_INFO("ADSBee::Update", "New message: 0x%08x|%06x SRC=%d SIGS=%ddBm SIGQ=%ddB MLAT=%u",
        //                  raw_packet.buffer[0], (raw_packet.buffer[1]) >> (2 * kBitsPerNibble), raw_packet.source,
        //                  raw_packet.sigs_dbm, raw_packet.sigq_db, raw_packet.mlat_48mhz_64bit_counts);
        // }

        // Decoded1090Packet decoded_packet = Decoded1090Packet(raw_packet);

        CONSOLE_INFO("ADSBee::Update", "\tdf=%d icao_address=0x%06x", decoded_packet.GetDownlinkFormat(),
                     decoded_packet.GetICAOAddress());

        if (aircraft_dictionary.IngestDecoded1090Packet(decoded_packet)) {
            // Packet was used to update the dictionary or was silently ignored (but presumed to be valid).
            FlashStatusLED();
            // NOTE: Pushing to the reporting queue here means that we only will report validated packets!
            // comms_manager.transponder_packet_reporting_queue.Push(decoded_packet);
            CONSOLE_INFO("ADSBee::Update", "\taircraft_dictionary: %d aircraft", aircraft_dictionary.GetNumAircraft());
        }
        comms_manager.transponder_packet_reporting_queue.Push(decoded_packet);
    }

    // Update trigger level learning if it's active.
    if (tl_learning_temperature_mv_ > 0 &&
        timestamp_ms - tl_learning_cycle_start_timestamp_ms_ > kTLLearningIntervalMs) {
        // Trigger level learning is active and due for an update.
        // Is this neighbor (current value for tl_mv) worth traversing to?
        float valid_packet_ratio = (tl_learning_num_valid_packets_ - tl_learning_prev_num_valid_packets_) /
                                   MAX(tl_learning_prev_num_valid_packets_, 1);  // Avoid divide by zero.
        float random_weight =
            static_cast<int16_t>(get_rand_32()) * kInt16MaxRecip * 0.25;  // Random value from [-0.25,0.25].
        if (valid_packet_ratio + random_weight > 0.0f) {
            // Transition to neighbor TL value.
            tl_learning_prev_tl_mv_ = tl_mv_;
            tl_learning_prev_num_valid_packets_ = tl_learning_num_valid_packets_;
        }
        // Else keep existing TL value in tl_learning_prev_tl_mv_.

        // DO STUFF HERE
        // Find a new neighbor by stepping trigger level with random value from [-1.0, 1.0] * temperature.
        uint16_t new_tl_mv = tl_mv_ + static_cast<int16_t>(get_rand_32()) * tl_learning_temperature_mv_ / INT16_MAX;
        if (new_tl_mv > tl_learning_max_mv_) {
            tl_mv_ = tl_learning_max_mv_;
        } else if (new_tl_mv < tl_learning_min_mv_) {
            tl_mv_ = tl_learning_min_mv_;
        } else {
            tl_mv_ = new_tl_mv;
        }

        // Update learning temperature. Decrement by the annealing temperature step or set to 0
        // if learning is complete.
        if (tl_learning_temperature_mv_ > tl_learning_temperature_step_mv_) {
            // Not done learning: step the trigger level learning temperature.
            tl_learning_temperature_mv_ -= tl_learning_temperature_step_mv_;
        } else {
            // Done learning: take the current best trigger level and yeet outta here.
            tl_learning_temperature_mv_ = 0;   // Set learning temperature to 0 to finish learnign trigger level.
            tl_mv_ = tl_learning_prev_tl_mv_;  // Set trigger level to the best value we've seen so far.
        }

        // Store timestamp as start of trigger learning cycle so we know when to come back.
        tl_learning_cycle_start_timestamp_ms_ = timestamp_ms;
        tl_learning_num_valid_packets_ = 0;  // Start the counter over.
    }

    // Update PWM output duty cycle.
    pwm_set_chan_level(tl_pwm_slice_, tl_pwm_chan_, tl_pwm_count_);

    // Occasionally sample the signal strength to approximate the noise floor.
    timestamp_ms = get_time_since_boot_ms();
    if (timestamp_ms - noise_floor_last_sample_timestamp_ms_ > kNoiseFloorADCSampleIntervalMs) {
        noise_floor_mv_ = ((noise_floor_mv_ * kNoiseFloorExpoFilterPercent) +
                           ReadSignalStrengthMilliVolts() * (100 - kNoiseFloorExpoFilterPercent)) /
                          100;
        noise_floor_last_sample_timestamp_ms_ = timestamp_ms;
    }
    return true;
}

void ADSBee::FlashStatusLED(uint32_t led_on_ms) {
    SetStatusLED(true);
    led_on_timestamp_ms_ = get_time_since_boot_ms();
}

uint64_t ADSBee::GetMLAT48MHzCounts(uint16_t num_bits) {
    // Combine the wrap counter with the current value of the SysTick register and mask to 48 bits.
    // Note: 24-bit SysTick value is subtracted from UINT_24_MAX to make it count up instead of down.
    return (mlat_counter_1s_wraps_ << 24 | (0xFFFFFF - systick_hw->cvr)) & (UINT64_MAX >> (64 - num_bits));
}

uint64_t ADSBee::GetMLAT12MHzCounts(uint16_t num_bits) {
    // Piggyback off the higher resolution 48MHz timer function.
    return GetMLAT48MHzCounts(50) >> 2;  // Divide 48MHz counter by 4, widen the mask by 2 bits to compensate.
}

int ADSBee::GetNoiseFloordBm() { return AD8313MilliVoltsTodBm(noise_floor_mv_); }

uint16_t ADSBee::GetTLLearningTemperatureMV() { return tl_learning_temperature_mv_; }

void ADSBee::OnDemodBegin(uint gpio) {
    uint16_t sm_index;
    for (sm_index = 0; sm_index < kNumDemodStateMachines; sm_index++) {
        if (config_.demod_pins[sm_index] == gpio) {
            break;
        }
    }
    if (sm_index >= kNumDemodStateMachines) return;  // Ignore; wasn't the start of a demod interval for a known SM.
    // Demodulation period is beginning!
    // Store the MLAT counter.
    rx_packet_[sm_index].mlat_48mhz_64bit_counts = GetMLAT48MHzCounts();  // TODO: have separate RX packets
}

void ADSBee::OnDemodComplete() {
    for (uint16_t sm_index = 0; sm_index < kNumDemodStateMachines; sm_index++) {
        if (!pio_interrupt_get(config_.preamble_detector_pio, sm_index)) {
            continue;
        }
        pio_sm_set_enabled(config_.message_demodulator_pio, message_demodulator_sm_[sm_index], false);
        // Read the RSSI level of the current packet.
        rx_packet_[sm_index].sigs_dbm = ReadSignalStrengthdBm();
        rx_packet_[sm_index].sigq_db = rx_packet_[sm_index].sigs_dbm - GetNoiseFloordBm();
        rx_packet_[sm_index].source = sm_index;  // Record this state machine as the source of the packet.
        if (!pio_sm_is_rx_fifo_full(config_.message_demodulator_pio, message_demodulator_sm_[sm_index])) {
            // Push any partially complete 32-bit word onto the RX FIFO.
            pio_sm_exec_wait_blocking(config_.message_demodulator_pio, message_demodulator_sm_[sm_index],
                                      pio_encode_push(false, true));
        }

        // Clear the transponder packet buffer.
        memset((void *)rx_packet_[sm_index].buffer, 0x0, Raw1090Packet::kMaxPacketLenWords32);

        // Pull all words out of the RX FIFO.
        volatile uint16_t packet_num_words =
            pio_sm_get_rx_fifo_level(config_.message_demodulator_pio, message_demodulator_sm_[sm_index]);
        if (packet_num_words > Raw1090Packet::kMaxPacketLenWords32) {
            // Packet length is invalid; dump everything and try again next time.
            // Only enable this print for debugging! Printing from the interrupt causes the USB library to crash.
            // CONSOLE_WARNING("ADSBee::OnDemodComplete", "Received a packet with %d 32-bit words, expected maximum of
            // %d.",
            //                 packet_num_words, Decoded1090Packet::kExtendedSquitterPacketNumWords32);
            // pio_sm_clear_fifos(config_.message_demodulator_pio, message_demodulator_sm_);
            packet_num_words = Raw1090Packet::kMaxPacketLenWords32;
        }
        // Track that we attempted to demodulate something.
        aircraft_dictionary.Record1090Demod();
        // Create a Raw1090Packet and push it onto the queue.
        for (uint16_t i = 0; i < packet_num_words; i++) {
            rx_packet_[sm_index].buffer[i] =
                pio_sm_get(config_.message_demodulator_pio, message_demodulator_sm_[sm_index]);
            if (i == packet_num_words - 1) {
                // // Trim off extra ingested bit from last word in the packet.
                // word  = word >> 1;
                // Mask and left align final word based on bit length.
                switch (packet_num_words) {
                    case Decoded1090Packet::kSquitterPacketNumWords32:
                        aircraft_dictionary.Record1090RawSquitterFrame();
                        rx_packet_[sm_index].buffer[i] = (rx_packet_[sm_index].buffer[i] & 0xFFFFFF) << 8;
                        rx_packet_[sm_index].buffer_len_bits = Decoded1090Packet::kSquitterPacketLenBits;
                        // raw_1090_packet_queue.Push(rx_packet_[sm_index]);
                        decoder.raw_1090_packet_in_queue.Push(rx_packet_[sm_index]);
                        break;
                    case Decoded1090Packet::kExtendedSquitterPacketNumWords32:
                        aircraft_dictionary.Record1090RawExtendedSquitterFrame();
                        rx_packet_[sm_index].buffer[i] = (rx_packet_[sm_index].buffer[i] & 0xFFFF) << 16;
                        rx_packet_[sm_index].buffer_len_bits = Decoded1090Packet::kExtendedSquitterPacketLenBits;
                        // raw_1090_packet_queue.Push(rx_packet_[sm_index]);
                        decoder.raw_1090_packet_in_queue.Push(rx_packet_[sm_index]);
                        break;
                    default:
                        // Don't push partial packets.
                        // Printing to tinyUSB from within an interrupt causes crashes! Don't do it.
                        // CONSOLE_WARNING(
                        //     "ADSBee::OnDemodComplete",
                        //     "Unhandled case while creating Raw1090Packet, received packet with %d 32-bit
                        //     words.", packet_num_words);
                        break;
                }
            }
        }

        // Clear the FIFO by pushing partial word from ISR, not bothering to block if FIFO is full (it shouldn't be).
        pio_sm_exec_wait_blocking(config_.message_demodulator_pio, message_demodulator_sm_[sm_index],
                                  pio_encode_push(false, false));
        while (!pio_sm_is_rx_fifo_empty(config_.message_demodulator_pio, message_demodulator_sm_[sm_index])) {
            pio_sm_get(config_.message_demodulator_pio, message_demodulator_sm_[sm_index]);
        }

        // Reset the demodulator state machine to wait for the next decode interval, then enable it.
        pio_sm_restart(config_.message_demodulator_pio, message_demodulator_sm_[sm_index]);  // Reset FIFOs, ISRs, etc.
        // The high power demodulator has a different start address to account for the fact that the index of its DEMOD
        // pin is different. This only matters for the initial program wait, subsequent demod checks are done on the
        // full GPIO input register.
        uint demodulator_program_start =
            sm_index == kHighPowerDemodStateMachineIndex
                ? message_demodulator_offset_ + message_demodulator_offset_high_power_initial_entry
                : message_demodulator_offset_ + message_demodulator_offset_initial_entry;
        pio_sm_exec_wait_blocking(config_.message_demodulator_pio, message_demodulator_sm_[sm_index],
                                  pio_encode_jmp(demodulator_program_start));  // Jump to beginning of program.
        pio_sm_set_enabled(config_.message_demodulator_pio, message_demodulator_sm_[sm_index], true);

        // Release the preamble detector from its wait state.
        if (sm_index == kHighPowerDemodStateMachineIndex) {
            // High power state machine operates alone and doesn't need to wait for any other SM to complete. It would
            // normally be enabled by one of the interleaved well formed preamble detector state machines refreshin, but
            // doing it here brings it up a little quicker and allows it to catch a subsequent high power packet if it
            // comes in quickly.
            pio_sm_exec_wait_blocking(
                config_.preamble_detector_pio, preamble_detector_sm_[sm_index],
                pio_encode_jmp(preamble_detector_offset_ + preamble_detector_offset_waiting_for_first_edge));
        }

        pio_interrupt_clear(config_.preamble_detector_pio, sm_index);

        // Reset the preamble detector state machine so that it starts looking for a new message.
        // pio_sm_restart(config_.preamble_detector_pio, preamble_detector_sm_[sm_index]);  // Reset FIFOs, ISRs, etc.
        // pio_sm_exec_wait_blocking(config_.preamble_detector_pio, preamble_detector_sm_[sm_index],
        //                           pio_encode_jmp(preamble_detector_offset_ +
        //                                          preamble_detector_offset_follow_irq));  // Jump to beginning of
        //                                          program.
        // pio_sm_set_enabled(config_.preamble_detector_pio, preamble_detector_sm_[sm_index], true);
    }
}

void ADSBee::OnSysTickWrap() { mlat_counter_1s_wraps_++; }

int ADSBee::ReadSignalStrengthMilliVolts() {
    adc_select_input(config_.rssi_adc_input);
    int rssi_adc_counts = adc_read();
    return rssi_adc_counts * 3300 / 4095;
}

int ADSBee::ReadSignalStrengthdBm() { return AD8313MilliVoltsTodBm(ReadSignalStrengthMilliVolts()); }

int ADSBee::ReadTLMilliVolts() {
    // Read back the low level TL bias output voltage.
    adc_select_input(config_.tl_adc_input);
    tl_adc_counts_ = adc_read();
    return ADCCountsToMilliVolts(tl_adc_counts_);
}

bool ADSBee::SetTLMilliVolts(int tl_mv) {
    if (tl_mv > kTLMaxMV || tl_mv < kTLMinMV) {
        CONSOLE_ERROR("ADSBee::SetTLMilliVolts", "Unable to set tl_mv_ to %d, outside of permissible range %d-%d.\r\n",
                      tl_mv, kTLMinMV, kTLMaxMV);
        return false;
    }
    tl_mv_ = tl_mv;
    tl_pwm_count_ = tl_mv_ * kTLMaxPWMCount / kVDDMV;

    return true;
}

void ADSBee::StartTLLearning(uint16_t tl_learning_num_cycles, uint16_t tl_learning_start_temperature_mv,
                             uint16_t tl_min_mv, uint16_t tl_max_mv) {
    tl_learning_temperature_mv_ = tl_learning_start_temperature_mv;
    tl_learning_temperature_step_mv_ = tl_learning_start_temperature_mv / tl_learning_num_cycles;
    tl_learning_cycle_start_timestamp_ms_ = get_time_since_boot_ms();
}
