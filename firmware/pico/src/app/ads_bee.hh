#ifndef _ADS_BEE_HH_
#define _ADS_BEE_HH_

#include "aircraft_dictionary.hh"
#include "cpp_at.hh"
#include "data_structures.hh"  // For PFBQueue.
#include "hardware/i2c.h"
#include "hardware/pio.h"
#include "macros.hh"  // For MAX / MIN.
#include "settings.hh"
#include "stdint.h"
#include "transponder_packet.hh"

class ADSBee {
   public:
    static constexpr uint16_t kTLMaxPWMCount = 5000;  // Clock is 125MHz, shoot for 25kHz PWM.
    static constexpr int kVDDMV = 3300;               // [mV] Voltage of positive supply rail.
    static constexpr int kTLMaxMV = 3300;             // [mV]
    static constexpr int kTLMinMV = 0;                // [mV]
    static const uint16_t kRxQueueLenWords = 20;
    static const uint32_t kRxQueuePacketDelimiter = 0x00000000;
    static constexpr uint16_t kMaxNumTransponderPackets =
        100;  // Defines size of ADSBPacket circular buffer (PFBQueue).
    static const uint32_t kStatusLEDOnMs = 10;
    static const uint16_t kNumDemodStateMachines = 2;

    struct ADSBeeConfig {
        PIO preamble_detector_pio = pio0;
        uint preamble_detector_demod_begin_irq = IO_IRQ_BANK0;
        PIO message_demodulator_pio = pio1;
        uint preamble_detector_demod_complete_irq = PIO0_IRQ_0;

        uint16_t status_led_pin = 15;
        // Reading ADS-B on GPIO19. Will look for DEMOD signal on GPIO20.
        uint16_t pulses_pins[kNumDemodStateMachines] = {19, 19};
        uint16_t demod_pins[kNumDemodStateMachines] = {20, 20};
        // Use GPIO22 for the decode PIO program to output its recovered clock (for debugging only).
        uint16_t recovered_clk_pins[kNumDemodStateMachines] = {22, 22};
        // GPIO 24-25 used as PWM outputs for setting analog comparator threshold voltages.
        uint16_t tl_pwm_pin = 25;
        // GPIO 26-27 used as ADC inputs for reading analog comparator threshold voltages after RF filer.
        uint16_t tl_adc_pin = 27;
        uint16_t tl_adc_input = 1;
        // GPIO 28 used as ADC input for the power level of the last decoded packet.
        uint16_t rssi_hold_adc_pin = 28;
        uint16_t rssi_hold_adc_input = 2;
        // GPIO 8 is used for clearing the RSSI peak detector.
        uint16_t rssi_clear_pin = 8;
        // GPIO 2-3 are used for the EEPROM and rx gain digipot I2C bus via I2C1.
        i2c_inst_t *onboard_i2c = i2c1;
        uint16_t onboard_i2c_sda_pin = 2;
        uint16_t onboard_i2c_scl_pin = 3;
        uint32_t onboard_i2c_clk_freq_hz = 400e3;  // 400kHz

        uint16_t uart_tx_pin = 4;
        uint16_t uart_rx_pin = 5;

        uint32_t aircraft_dictionary_update_interval_ms = 1000;
    };

    ADSBee(ADSBeeConfig config_in);
    bool Init();
    bool Update();

    void SetReceiverEnable(bool is_enabled) {
        is_enabled_ = is_enabled;
        irq_set_enabled(config_.preamble_detector_demod_complete_irq, is_enabled_);
    }

    bool ReceiverIsEnabled() { return is_enabled_; }

    /**
     * Blinks the status LED for a given number of milliseconds. Non-blocking.
     * @param[in] led_on_ms Optional parameter specifying number of milliseconds to turn on for. Defaults to
     * kStatusLEDOnMs.
     */
    void FlashStatusLED(uint32_t led_on_ms = kStatusLEDOnMs);

    /**
     * ISR for GPIO interrupts.
     */
    void OnDemodBegin(uint gpio, uint32_t event_mask);

    /**
     * Return the value of the low Minimum Trigger Level threshold in milliVolts.
     * @retval TL in milliVolts.
     */
    int GetTLMilliVolts() { return tl_mv_; }

    /**
     * ISR triggered by DECODE completing, via PIO0 IRQ0.
     */
    void OnDemodComplete();

    /**
     * ISR triggered by SysTick interrupt. Used to wrap the MLAT counter.
     */
    void OnSysTickWrap();

    /**
     * Creates a composite timestamp using the current value of the SysTick timer (running at 125MHz) and the SysTick
     * wrap counter to simulate a timer running at 48MHz (which matches the frequency of the preamble detector PIO).
     * @param[in] num_bits Number of bits to mask the counter value to. Defaults to full resolution.
     * @retval 48MHz counter value.
     */
    inline uint64_t GetMLAT48MHzCounts(uint16_t num_bits = 64);

    /**
     * Creates a composite timestamp using the current value of the SysTick timer (running at 125MHz) and the SysTick
     * wrap counter to simulate a timer running at 12MHz, which matches existing decoders that use the Mode S Beast
     * protocol.
     * @param[in] num_bits Number of bits to mask the counter value to. Defaults to 48 bits (6 Bytes) to match Mode S
     * Beast protocol.
     * @retval 48MHz counter value.
     */
    inline uint64_t GetMLAT12MHzCounts(uint16_t num_bits = 48);

    /**
     * Read the high Minimum Trigger Level threshold via ADC.
     * @retval TL in milliVolts.
     */
    int ReadTLHiMilliVolts();

    /**
     * Read the low Minimum Trigger Level threshold via ADC.
     * @retval TL in milliVolts.
     */
    int ReadTLMilliVolts();

    /**
     * Set the high Minimum Trigger Level (TL) at the AD8314 output in milliVolts.
     * @param[in] tl_hi_mv Voltage level for a "high" trigger on the V_DN AD8314 output. The AD8314 has a nominal
     * output voltage of 2.25V on V_DN, with a logarithmic slope of around -42.6mV/dB and a minimum output voltage of
     * 0.05V. Thus, power levels received at the input of the AD8314 correspond to the following voltages. 2250mV =
     * -49dBm 50mV = -2.6dBm Note that there is a +30dB LNA gain stage in front of the AD8314, so for the overall
     * receiver, the TL values are more like: 2250mV = -79dBm 50mV = -32.6dBm
     * @retval True if succeeded, False if TL value was out of range.
     */
    bool SetTLHiMilliVolts(int tl_hi_mv);

    /**
     * Set the low Minimum Trigger Level (TL) at the AD8314 output in milliVolts.
     * @param[in] tl_mv Voltage level for a "low" trigger on the V_DN AD8314 output. The AD8314 has a nominal
     * output voltage of 2.25V on V_DN, with a logarithmic slope of around -42.6mV/dB and a minimum output voltage of
     * 0.05V. Thus, power levels received at the input of the AD8314 correspond to the following voltages. 2250mV =
     * -49dBm 50mV = -2.6dBm Note that there is a +30dB LNA gain stage in front of the AD8314, so for the overall
     * receiver, the TL values are more like: 2250mV = -79dBm 50mV = -32.6dBm
     * @retval True if succeeded, False if TL value was out of range.
     */
    bool SetTLMilliVolts(int tl_mv);

    /**
     * Returns the Receive Signal Strength Indicator (RSSI) of the message that is currently being read, in dBm.
     */
    int ReadRSSIdBm();

    PFBQueue<RawTransponderPacket> transponder_packet_queue = PFBQueue<RawTransponderPacket>(
        {.buf_len_num_elements = kMaxNumTransponderPackets, .buffer = transponder_packet_queue_buffer_});

    AircraftDictionary aircraft_dictionary;

   private:
    ADSBeeConfig config_;
    CppAT parser_;

    uint32_t preamble_detector_sm_ = 0;
    uint32_t preamble_detector_offset_ = 0;

    uint32_t message_demodulator_sm_ = 0;
    uint32_t message_demodulator_offset_ = 0;

    uint32_t led_off_timestamp_ms_ = 0;

    uint16_t tl_pwm_slice_ = 0;
    uint16_t tl_pwm_chan_ = 0;

    uint16_t tl_mv_ = SettingsManager::kDefaultTLMV;
    uint16_t tl_pwm_count_ = 0;  // out of kTLMaxPWMCount

    uint16_t tl_adc_counts_ = 0;

    uint32_t mlat_counter_1s_wraps_ = 0;

    RawTransponderPacket rx_packet_;
    RawTransponderPacket transponder_packet_queue_buffer_[kMaxNumTransponderPackets];

    uint32_t last_aircraft_dictionary_update_timestamp_ms_ = 0;
    uint16_t last_demod_num_words_ingested_ = 0;

    bool is_enabled_ = true;
};

extern ADSBee ads_bee;

#endif /* _ADS_BEE_HH_ */