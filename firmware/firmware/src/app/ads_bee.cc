#include "ads_bee.hh"

#include <stdio.h>  // for printing

#include "hardware/adc.h"
#include "hardware/clocks.h"
#include "hardware/gpio.h"
#include "hardware/pio.h"
#include "hardware/pwm.h"
#include "pico/stdlib.h"
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
const uint8_t kEEPROMI2CAddr = 0b1010001;  // M24C02, TSSOP-8, E3=0 E2=0 E1=1

ADSBee *isr_access = NULL;

void on_decode_complete() { isr_access->OnDecodeComplete(); }

/** I2C helper function that writes 1 byte to the specified register.
 * @param[in] i2c Pico SDK i2c_inst_t to use.
 * @param[in] addr I2C address (device) to write to.
 * @param[in] reg Register address (on the device) to write to.
 * @param[in] buf Byte buffer to write to the given address.
 * @param[in] nbytes Number of bytes to write to the given address on the device.
 */
inline int i2c_reg_write(i2c_inst_t *i2c, const uint addr, const uint8_t reg, uint8_t *buf, const uint8_t nbytes) {
    int num_bytes_read = 0;
    uint8_t msg[nbytes + 1];

    // Check to make sure caller is sending 1 or more bytes
    if (nbytes < 1) {
        return 0;
    }

    // Append register address to front of data packet
    msg[0] = reg;
    for (int i = 0; i < nbytes; i++) {
        msg[i + 1] = buf[i];
    }

    // Write data to register(s) over I2C
    i2c_write_blocking(i2c, addr, msg, (nbytes + 1), false);

    return num_bytes_read;
}

/** Read byte(s) from the specified register. If nbytes > 1, read from consecutive registers.
 * @param[in] i2c Pico SDK i2c_inst_t to use.
 * @param[in] addr I2C address (device) to read from.
 * @param[in] reg Register address (on the device) to read from.
 * @param[in] buf Byte buffer to read into from the given address.
 * @param[in] nbytes Number of bytes to read from the device.
 */
inline int i2c_reg_read(i2c_inst_t *i2c, const uint addr, const uint8_t reg, uint8_t *buf, const uint8_t nbytes) {
    int num_bytes_read = 0;

    // Check to make sure caller is asking for 1 or more bytes
    if (nbytes < 1) {
        return 0;
    }

    // Read data from register(s) over I2C
    i2c_write_blocking(i2c, addr, &reg, 1, true);
    num_bytes_read = i2c_read_blocking(i2c, addr, buf, nbytes, false);

    return num_bytes_read;
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
    mtl_lo_pwm_slice_ = pwm_gpio_to_slice_num(config_.mtl_lo_pwm_pin);
    mtl_hi_pwm_slice_ = pwm_gpio_to_slice_num(config_.mtl_hi_pwm_pin);
    mtl_lo_pwm_chan_ = pwm_gpio_to_channel(config_.mtl_lo_pwm_pin);
    mtl_hi_pwm_chan_ = pwm_gpio_to_channel(config_.mtl_hi_pwm_pin);
}

bool ADSBee::Init() {
    // Initialize the MTL bias PWM output.
    gpio_set_function(config_.mtl_lo_pwm_pin, GPIO_FUNC_PWM);
    gpio_set_function(config_.mtl_hi_pwm_pin, GPIO_FUNC_PWM);
    pwm_set_wrap(mtl_lo_pwm_slice_, kMTLMaxPWMCount);
    pwm_set_wrap(mtl_hi_pwm_slice_, kMTLMaxPWMCount);  // redundant since it's the same slice

    SetMTLLoMilliVolts(kMTLLoDefaultMV);
    SetMTLHiMilliVolts(kMTLHiDefaultMV);
    pwm_set_enabled(mtl_lo_pwm_slice_, true);
    pwm_set_enabled(mtl_hi_pwm_slice_, true);  // redundant since it's the same slice

    // Initialize the ML bias ADC input.
    adc_init();
    adc_gpio_init(config_.mtl_lo_adc_pin);
    adc_gpio_init(config_.mtl_hi_adc_pin);
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
        DEBUG_PRINTF("ADSBee::Init: Failed to read wiper position from Rx Gain Digipot at I2C address 0x%x.\r\n",
                     kRxGainDigipotI2CAddr);
        return false;
    }
    uint8_t eeprom_random_address_data;
    if (i2c_read_blocking(config_.onboard_i2c, kEEPROMI2CAddr, &eeprom_random_address_data, 1, false) != 1) {
        DEBUG_PRINTF("ADSBee::Init: Failed to read current address from EEPROM at I2C address 0x%x.\r\n",
                     kEEPROMI2CAddr);
        return false;
    }

    // Initialize ESP32 GPIOs.
    gpio_init(config_.esp32_enable_pin);
    gpio_set_dir(config_.esp32_enable_pin, GPIO_OUT);
    gpio_put(config_.esp32_enable_pin, 0);  // Disable ESP32.

    gpio_init(config_.esp32_gpio0_boot_pin);
    gpio_set_dir(config_.esp32_gpio0_boot_pin, GPIO_OUT);
    gpio_put(config_.esp32_gpio0_boot_pin, 1);  // Disable ESP32 download boot mode.

    // Calculate the PIO clock divider.
    float preamble_detector_div = (float)clock_get_hz(clk_sys) / kPreambleDetectorFreq;

    // Initialize the program using the .pio file helper function
    preamble_detector_program_init(config_.preamble_detector_pio, preamble_detector_sm_, preamble_detector_offset_,
                                   config_.pulses_pin, config_.decode_out_pin, preamble_detector_div);

    // enable the DECODE interrupt on PIO0_IRQ_0
    uint preamble_detector_decode_irq = PIO0_IRQ_0;
    pio_set_irq0_source_enabled(config_.preamble_detector_pio, pis_interrupt0, true);  // state machine 0 IRQ 0

    /** MESSAGE DECODER PIO **/
    float message_decoder_freq = 16e6;  // Run at 32 MHz to decode bits at 1Mbps.
    float message_decoder_div = (float)clock_get_hz(clk_sys) / message_decoder_freq;
    message_decoder_program_init(config_.message_decoder_pio, message_decoder_sm_, message_decoder_offset_,
                                 config_.pulses_pin, config_.recovered_clk_pin, message_decoder_div);

    DEBUG_PRINTF("ADSBee::Init: PIOs initialized.\r\n");

    gpio_init(config_.status_led_pin);
    gpio_set_dir(config_.status_led_pin, GPIO_OUT);

    // FIXME: this doesn't work yet. Can an std::function be used as a (void *)?
    // irq_set_exclusive_handler(
    //     preamble_detector_decode_irq,
    //     std::bind(
    //         &ADSBee::OnDecodeComplete,
    //         this
    //     )
    // );
    irq_set_exclusive_handler(preamble_detector_decode_irq, on_decode_complete);
    irq_set_enabled(preamble_detector_decode_irq, true);

    // Enable the state machines
    pio_sm_set_enabled(config_.preamble_detector_pio, preamble_detector_sm_, true);
    pio_sm_set_enabled(config_.message_decoder_pio, message_decoder_sm_, true);

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
    // Turn off the decode LED if it's been on for long enough.
    if (get_time_since_boot_ms() > led_off_timestamp_ms_) {
        gpio_put(config_.status_led_pin, 0);
    }

    // Update PWM output duty cycle.
    pwm_set_chan_level(mtl_lo_pwm_slice_, mtl_lo_pwm_chan_, mtl_lo_pwm_count_);
    pwm_set_chan_level(mtl_hi_pwm_slice_, mtl_hi_pwm_chan_, mtl_hi_pwm_count_);
    return true;
}

void ADSBee::OnDecodeComplete() {
    pio_interrupt_clear(config_.preamble_detector_pio, 0);

    // Read the RSSI level of the last packet.
    adc_select_input(config_.rssi_hold_adc_input);
    rssi_adc_counts_ = adc_read();
    gpio_put(config_.rssi_clear_pin, 0);  // Clear RSSI peak detector.
    // Put RSSI clear HI later, to give peak detector some time to drain.

    uint16_t word_index = 0;
    while (!pio_sm_is_rx_fifo_empty(config_.message_decoder_pio, message_decoder_sm_)) {
        uint32_t word = pio_sm_get(config_.message_decoder_pio, message_decoder_sm_);
        DEBUG_PRINTF("\t%d: %08x\r\n", word_index, word);

        switch (word_index) {
            case 0: {
                // Flush the previous word into a packet before beginning to store the new one.

                // First word out of the FIFO is actually the last word of the previously decoded message.
                // Assemble a packet buffer using the items in rx_buffer_.
                uint32_t packet_buffer[ADSBPacket::kMaxPacketLenWords32];
                packet_buffer[0] = rx_buffer_[0];
                packet_buffer[1] = rx_buffer_[1];
                packet_buffer[2] = rx_buffer_[2];
                // Trim extra ingested bit off of last word, then left-align.
                packet_buffer[3] = (static_cast<uint16_t>(word >> 1)) << 16;
                ADSBPacket packet = ADSBPacket(packet_buffer, ADSBPacket::kMaxPacketLenWords32, rssi_adc_counts_);
                adsb_packet_queue.Push(packet);
                // DEBUG_PRINTF(packet.IsValid() ? "\tVALID\r\n": "\tINVALID\r\n");
                break;
            }
            case 1:
            case 2:
            case 3:
                rx_buffer_[word_index - 1] = word;
                break;
                // case 3:
                //     // Last word ingests an extra bit by accident, pinch it off here.
                //     rx_buffer_[word_index-1] = word>>1;

                break;
            default:
                // Received too many bits for this to be a valid packet. Throw away extra bits!
                DEBUG_PRINTF("tossing\r\n");
                pio_sm_get(config_.message_decoder_pio, message_decoder_sm_);  // throw away extra bits
        }
        word_index++;
    }

    gpio_put(config_.rssi_clear_pin, 1);  // restore RSSI peak detector to working order.
    pio_interrupt_clear(config_.preamble_detector_pio, 0);
}

bool ADSBee::SetMTLHiMilliVolts(int mtl_hi_mv_) {
    if (mtl_hi_mv_ > kMTLMaxMV || mtl_hi_mv_ < kMTLMinMV) {
        DEBUG_PRINTF(
            "ADSBee::SetMTLHiMilliVolts: Unable to set mtl_hi_mv_ to %d, outside of permissible range %d-%d.\r\n",
            mtl_hi_mv_, kMTLMinMV, kMTLMaxMV);
        return false;
    }
    mtl_hi_mv_ = mtl_hi_mv_;
    mtl_hi_pwm_count_ = mtl_hi_mv_ * kMTLMaxPWMCount / kVDDMV;

    return true;
}

bool ADSBee::SetMTLLoMilliVolts(int mtl_lo_mv_) {
    if (mtl_lo_mv_ > kMTLMaxMV || mtl_lo_mv_ < kMTLMinMV) {
        DEBUG_PRINTF(
            "ADSBee::SetMTLLoMilliVolts: Unable to set mtl_lo_mv_ to %d, outside of permissible range %d-%d.\r\n",
            mtl_lo_mv_, kMTLMinMV, kMTLMaxMV);
        return false;
    }
    mtl_lo_mv_ = mtl_lo_mv_;
    mtl_lo_pwm_count_ = mtl_lo_mv_ * kMTLMaxPWMCount / kVDDMV;

    return true;
}

inline int adc_counts_to_mv(uint16_t adc_counts) { return 3300 * adc_counts / 0xFFF; }

int ADSBee::ReadMTLHiMilliVolts() {
    // Read back the high level MTL bias output voltage.
    adc_select_input(config_.mtl_hi_adc_input);
    mtl_hi_adc_counts_ = adc_read();
    return adc_counts_to_mv(mtl_hi_adc_counts_);
}

int ADSBee::ReadMTLLoMilliVolts() {
    // Read back the low level MTL bias output voltage.
    adc_select_input(config_.mtl_lo_adc_input);
    mtl_lo_adc_counts_ = adc_read();
    return adc_counts_to_mv(mtl_lo_adc_counts_);
}

bool ADSBee::SetRxGain(int rx_gain) {
    rx_gain_digipot_resistance_ohms_ = (rx_gain - 1) * 1e3;  // Non-inverting amp with R1 = 1kOhms.
    uint8_t wiper_value_counts = (rx_gain_digipot_resistance_ohms_ / kRxgainDigipotOhmsPerCount);
    return i2c_write_blocking(config_.onboard_i2c, kRxGainDigipotI2CAddr, &wiper_value_counts, 1, false) == 1;
    // uint8_t buf = (uint8_t)rx_gain;
    // return i2c_write_blocking(config_.onboard_i2c, kRxGainDigipotI2CAddr, &buf, 1, false) == 1;
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