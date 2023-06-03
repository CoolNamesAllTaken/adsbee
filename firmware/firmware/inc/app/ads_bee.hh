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

        uint led_pin = 25;
        uint pulses_pin = 19; // Reading ADS-B on GPIO22. Will look for DECODE signal on GPIO22-1 = GPIO21.
        uint decode_in_pin = pulses_pin+1;
        uint decode_out_pin = 21; // Use GPIO20 as DECODE signal output, will be wired to GPIO21 as input.
    };

    ADSBee(ADSBeeConfig config_in);
    void Init();
    void Update();
    void OnDecodeComplete();
private:
    ADSBeeConfig config_;

    uint preamble_detector_sm_ = 0;
    uint preamble_detector_offset_ = 0;

    uint message_decoder_sm_ = 0;
    uint message_decoder_offset_ = 0;

    uint32_t led_off_timestamp_ms_ = 0;

    uint32_t rx_buffer_[ADSBPacket::kMaxPacketLenWords32];
    
};

#endif /* _ADS_BEE_HH_ */