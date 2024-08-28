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
    static const uint32_t kStatsUpdateIntervalMs = 1000;  // [ms] How often statistics update.

    static const uint32_t kTLLearningIntervalMs =
        10000;  // [ms] Length of Simulated Annealing interval for learning trigger level.
    static const uint16_t kTLLearningNumCycles =
        100;  // Number of simulated annealing cycles for learning trigger level.
    static const uint16_t kTLLearningStartTemperatureMV =
        1000;  // [mV] Starting value for simulated annealing temperature when learning triger level. This corresponds
               // to the maximum value that the trigger level could be moved (up or down) when exploring a neighbor
               // state.

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
        uint16_t rssi_adc_pin = 28;
        uint16_t rssi_adc_input = 2;
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
     * Get the current temperature used in learning trigger level (simulated annealing). A temperature of 0 means
     * learning has completed.
     * @retval Current temperature used for simulated annealing, in milliVolts.
     */
    uint16_t GetTLLearningTemperatureMV();

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
     * Start learning the trigger level through Simulated Annealing. Will begin kTLLearningNumCycles annealing cycles
     * with an annealing interval of kTLLearningIntervalMs milliseconds. Can be provided with maximum and minimum
     * trigger level bounds to allow a narrower search.
     * @param[in] tl_learning_num_cycles Number of cycles to use while annealing trigger level (sets the amount that the
     * annealing temperature is decreased each cycle). Optional, defaults to kTLLearningNumCycles.
     * @param[in] tl_learning_start_temperature_mv Annealing temperature to start with, in mV.
     * @param[in] tl_min_mv Minimum trigger level to use while learning, in milliVolts. Optional, defaults to full scale
     * (kTLMinMV).
     * @param[in] tl_max_mv Maximum trigger level to use while learning, in milliVolts. Optional, defaults to full scale
     * (kTLMaxMV).
     */
    void StartTLLearning(uint16_t tl_learning_num_cycles = kTLLearningNumCycles,
                         uint16_t tl_learning_start_temperature_mv = kTLLearningStartTemperatureMV,
                         uint16_t tl_min_mv = kTLMinMV, uint16_t tl_max_mv = kTLMaxMV);

    /**
     * Returns the Receive Signal Strength Indicator (RSSI) of the signal currently provided by the RF power detector,
     * in mV.
     * @retval Voltage from the RF power detector, in mV.
     */
    inline int ReadRSSIMilliVolts();

    /**
     * Returns the Receive Signal Strength Indicator (RSSI) of the message that is currently being provided by the RF
     * power detector, in dBm. makes use of ReadRSSIMilliVolts().
     * @retval Voltage form the RF power detector converted to dBm using the chart in the AD8313 datasheet.
     */
    inline int ReadRSSIdBm();

    /**
     * Returns the number of demodulations attempted in the last kStatsUpdateIntervalMs milliseconds.
     * @retval Number of demods attempted.
     */
    inline uint16_t GetStatsNumDemods() { return stats_num_demods_; }

    /**
     * Returns the number of valid Mode A / Mode C packets decoded in the last kStatsUpdateIntervalMs milliseconds.
     * @retval Number of valid packets received with Downlink Format = 4, 5.
     */
    inline uint16_t GetStatsNumModeACPackets() { return stats_num_valid_mode_ac_packets_; }

    /**
     * Returns the number of valid Mode S packets decoded in the last kStatsUpdateIntervalMs milliseconds.
     * @retval Number of valid packets received with Downlink Format != 4, 5.
     */
    inline uint16_t GetStatsNumModeSPackets() { return stats_num_valid_mode_s_packets_; }

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

    uint32_t led_on_timestamp_ms_ = 0;

    uint16_t tl_pwm_slice_ = 0;
    uint16_t tl_pwm_chan_ = 0;

    uint16_t tl_mv_ = SettingsManager::kDefaultTLMV;
    uint16_t tl_pwm_count_ = 0;  // out of kTLMaxPWMCount

    uint16_t tl_adc_counts_ = 0;

    uint32_t tl_learning_cycle_start_timestamp_ms_ = 0;
    uint16_t tl_learning_temperature_mv_ = 0;  // Don't learn automatically.
    int16_t tl_learning_temperature_step_mv_ = 0;
    uint16_t tl_learning_max_mv_ = kTLMaxMV;
    uint16_t tl_learning_min_mv_ = kTLMinMV;
    int16_t tl_learning_num_valid_packets_ = 0;
    int16_t tl_learning_prev_num_valid_packets_ = 1;  // Set to 1 to avoid dividing by 0.
    uint16_t tl_learning_prev_tl_mv_ = tl_mv_;

    uint32_t mlat_counter_1s_wraps_ = 0;

    RawTransponderPacket rx_packet_;
    RawTransponderPacket transponder_packet_queue_buffer_[kMaxNumTransponderPackets];

    uint32_t last_aircraft_dictionary_update_timestamp_ms_ = 0;

    // These values are continuous counters of number of packets of each type received. Don't use these values for
    // anything external!
    uint16_t stats_num_demods_counter_ = 0;
    uint16_t stats_num_valid_mode_ac_packets_counter_ = 0;
    uint16_t stats_num_valid_mode_s_packets_counter_ = 0;

    // Timestamp of the last time that the packet counters were stored and reset to 0.
    uint32_t stats_last_update_timestamp_ms_ = 0;  // [ms]

    // These values are updated every stats update interval so that they always contain counts across a consistent
    // interval. Use these values for anything important!
    uint16_t stats_num_demods_ = 0;
    uint16_t stats_num_valid_mode_ac_packets_ = 0;
    uint16_t stats_num_valid_mode_s_packets_ = 0;

    bool is_enabled_ = true;
};

extern ADSBee ads_bee;

#endif /* _ADS_BEE_HH_ */