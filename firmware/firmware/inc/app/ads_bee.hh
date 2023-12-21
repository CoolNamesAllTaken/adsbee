#ifndef _ADS_BEE_HH_
#define _ADS_BEE_HH_

#include "hardware/pio.h"
#include "stdint.h"
#include "ads_b_packet.hh"

class ADSBee {
public:

    struct ADSBeeConfig {
        PIO preamble_detector_pio = pio0;
        PIO message_decoder_pio = pio1;

        uint16_t status_led_pin = 15;
        uint16_t pulses_pin = 19; // Reading ADS-B on GPIO22. Will look for DECODE signal on GPIO22-1 = GPIO21.
        uint16_t decode_in_pin = pulses_pin+1;
        uint16_t decode_out_pin = 21; // Use GPIO20 as DECODE signal output, will be wired to GPIO21 as input.
        uint16_t mtl_bias_pwm_pin = 16; // GPIO16 is PWM output for setting analog comparator bias voltage.
        uint16_t mtl_bias_adc_pin = 26; // GPIO26 is ADC input for reading analog comparator bias voltage after RC filter.
        uint16_t mtl_bias_adc_input = 0;

        uint16_t uart_tx_pin = 4;
        uint16_t uart_rx_pin = 5;
    };

    ADSBee(ADSBeeConfig config_in);
    void Init();
    void Update();
    void OnDecodeComplete();
    bool SetMTLMilliVolts(int mtl_threshold_mv);
    int GetMTLMilliVolts();
    bool SetMTLdBm(int mtl_threshold_dbm);

    const uint16_t kMTLBiasMaxPWMCount = 5000; // Clock is 125MHz, shoot for 25kHz PWM.
    const int kVDDMV = 3300; // [mV] Voltage of positive supply rail.
    const int kMTLBiasMaxMV = 2250; // [mV]
    const int kMTLBiasMinMV = 0; // [mV]
    const int kMTLBiasDefaultMV = 2000; // [mV]

    // Coefficients for calibrated polynomial equation to go from target MTL bias voltage to MTL bias PWM count.
    const float kMTLBiasPWMCompCoeffX3 = 4.87299E-08;
    const float kMTLBiasPWMCompCoeffX2 = -0.000376253;
    const float kMTLBiasPWMCompCoeffX = 2.496361699;
    const float kMTLBiasPWMCompCoeffConst = -16.0676799;

private:
    ADSBeeConfig config_;

    uint32_t preamble_detector_sm_ = 0;
    uint32_t preamble_detector_offset_ = 0;

    uint32_t message_decoder_sm_ = 0;
    uint32_t message_decoder_offset_ = 0;

    uint32_t led_off_timestamp_ms_ = 0;

    uint16_t mtl_bias_pwm_slice_ = 0;
    uint16_t mtl_bias_pwm_chan_ = 0;
    uint16_t mtl_bias_mv_ = kMTLBiasDefaultMV;
    uint16_t mtl_bias_pwm_count_ = 0; // Out of kMaxPWMCount.
    uint16_t mtl_bias_adc_counts_ = 0;

    uint32_t rx_buffer_[ADSBPacket::kMaxPacketLenWords32];
    
};

#endif /* _ADS_BEE_HH_ */