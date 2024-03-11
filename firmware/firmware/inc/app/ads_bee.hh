#ifndef _ADS_BEE_HH_
#define _ADS_BEE_HH_

#include "hardware/pio.h"
#include "stdint.h"
#include "ads_b_packet.hh"
#include "at_command_parser.hh"

class ADSBee {
public:

    struct ADSBeeConfig {
        PIO preamble_detector_pio = pio0;
        PIO message_decoder_pio = pio1;

        uint16_t status_led_pin = 15;
        uint16_t pulses_pin = 19; // Reading ADS-B on GPIO22. Will look for DECODE signal on GPIO22-1 = GPIO21.
        uint16_t decode_in_pin = pulses_pin+1;
        uint16_t decode_out_pin = 21; // Use GPIO20 as DECODE signal output, will be wired to GPIO21 as input.
        uint16_t recovered_clk_pin = 22; // Use GPIO22 for the decode PIO program to output its recovered clock (for debugging only).
        // GPIO 24-25 used as PWM outputs for setting analog comparator threshold voltages.
        uint16_t mtl_lo_pwm_pin = 24;
        uint16_t mtl_hi_pwm_pin = 25;
        // GPIO 26-27 used as ADC inputs for reading analog comparator threshold voltages after RF filer.
        uint16_t mtl_lo_adc_pin = 26;
        uint16_t mtl_lo_adc_input = 0;
        uint16_t mtl_hi_adc_pin = 27;
        uint16_t mtl_hi_adc_input = 1;
        // GPIO 28 used as ADC input for the power level of the last decoded packet.
        uint16_t rssi_hold_adc_pin = 28;
        uint16_t rssi_hold_adc_input = 2;
        // GPIO 8 is used for clearing the RSSI peak detector.
        uint16_t rssi_clear_pin = 8;

        uint16_t uart_tx_pin = 4;
        uint16_t uart_rx_pin = 5;
    };

    ADSBee(ADSBeeConfig config_in);
    void Init();
    void Update();
    void OnDecodeComplete();
    bool SetMTLHiMilliVolts(int mtl_hi_mv);
    bool SetMTLLoMilliVolts(int mtl_lo_mv);
    int GetMTLHiMilliVolts();
    int GetMTLLoMilliVolts();
    bool SetMTLdBm(int mtl_threshold_dbm);

    bool ATConfigCallback(char op, std::vector<std::string> args);
    bool ATMTLSetCallback(char op, std::vector<std::string> args);
    bool ATMTLReadCallback(char op, std::vector<std::string> args);

    typedef enum {
        RUN = 0,
        CONFIG = 1
    } ATConfigMode_t;

    const uint16_t kMTLMaxPWMCount = 5000; // Clock is 125MHz, shoot for 25kHz PWM.
    const int kVDDMV = 3300; // [mV] Voltage of positive supply rail.
    const int kMTLMaxMV = 2250; // [mV]
    const int kMTLMinMV = 0; // [mV]
    const int kMTLHiDefaultMV = 2000; // [mV]
    const int kMTLLoDefaultMV = 1500; // [mV]

    // Coefficients for calibrated polynomial equation to go from target MTL bias voltage to MTL bias PWM count.
    // const float kMTLBiasPWMCompCoeffX3 = 4.87299E-08;
    // const float kMTLBiasPWMCompCoeffX2 = -0.000376253;
    // const float kMTLBiasPWMCompCoeffX = 2.496361699;
    // const float kMTLBiasPWMCompCoeffConst = -16.0676799;

private:
    ADSBeeConfig config_;
    ATCommandParser parser_;

    uint32_t preamble_detector_sm_ = 0;
    uint32_t preamble_detector_offset_ = 0;

    uint32_t message_decoder_sm_ = 0;
    uint32_t message_decoder_offset_ = 0;

    uint32_t led_off_timestamp_ms_ = 0;

    uint16_t mtl_lo_pwm_slice_ = 0;
    uint16_t mtl_hi_pwm_slice_ = 0;
    uint16_t mtl_hi_pwm_chan_ = 0;
    uint16_t mtl_lo_pwm_chan_ = 0;
    uint16_t mtl_hi_mv_ = kMTLHiDefaultMV;
    uint16_t mtl_hi_pwm_count_ = 0; // out of kMTLMaxPWMCount
    uint16_t mtl_lo_mv_ = kMTLLoDefaultMV;
    uint16_t mtl_lo_pwm_count_ = 0; // out of kMTLMaxPWMCount

    uint16_t mtl_lo_adc_counts_ = 0;
    uint16_t mtl_hi_adc_counts_ = 0;
    uint16_t rssi_adc_counts_ = 0;

    // Due to a quirk, rx_buffer_ is used to store every word except for the first one.
    uint32_t rx_buffer_[ADSBPacket::kMaxPacketLenWords32-1];
    
    ATConfigMode_t at_config_mode_ = ATConfigMode_t::RUN;
    std::string at_command_buf_ = "";

    void InitATCommandParser();
};

#endif /* _ADS_BEE_HH_ */