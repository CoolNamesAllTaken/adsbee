#ifndef _ADS_B_DECODER_HH_
#define _ADS_B_DECODER_HH_

#include <stdint.h>

class ADSBDecoder {
public:
    static const uint16_t kRxQueueMaxLenWords = 10; // [Words] Length of received bits buffer.
    static const uint16_t kSamplesPerBit = 4; // Bitrate is 1Mbps, sample rate is 4Mbps.

    // Preamble detection matched filter coefficients.
    static const uint32_t mf_template_preamble = 0b00000000000011001100000000110011;
    static const uint16_t mf_template_preamble_len_bits = 32;
    int mf_coeff_11 = 1; // Matched filter coefficient for template bit = 1, message bit = 1.
    int mf_coeff_10 = -4; // Matched filter coefficient for template bit = 1, message bit = 0.
    int mf_coeff_01 = -4; // Matched filter coefficient for template bit = 0, message bit = 1.
    int mf_coeff_00 = 1; // Matched filter coefficient for template bit = 0, message bit = 0.
    int mf_ok_threshold = 5; // Threshold for determining a filter match.

    // Bit detection matched filter.
    static const uint32_t mf_template_0bit = 0b1100; // "0" bit is a rising edge

    ADSBDecoder(); // constructor

    // Rx queue functions.
    void ClearRxQueue();
    bool PushWord(uint32_t word); // Pushes a full word onto the rx queue. Returns True if the queue had space.
    uint16_t PopBits(uint16_t num_bits, uint32_t &buffer);
    uint16_t PeekBits(uint16_t num_bits, uint32_t &buffer);
    uint16_t GetRxQueueLenBits();

    // Preamble detection functions.
    bool FindPreamble();

    void Update(); // TODO: update to callback something if a preamble is found or message is completely decoded.

    // For debugging.
    uint16_t GetRxQueueFront() const { return rx_queue_front_; };
    uint16_t GetRxQueueRear() const { return rx_queue_rear_; };
    uint16_t GetRxQueueBitOffset() const { return rx_queue_bit_offset_; };

private:
    uint32_t rx_queue_[kRxQueueMaxLenWords+1]; // add extra slot to use for digesting a word into bits
    uint16_t rx_queue_front_ = 0; // word index of front of queue (oldest word)
    uint16_t rx_queue_rear_ = 0; // word index of rear of queue (newest word)
    uint16_t rx_queue_bit_offset_ = 0; // number of bits that have been popped off of the front word.
    uint16_t rx_queue_len_bits_ = 0; // number of bits currently in the queue

    typedef enum {
        FALLING_EDGE = 0b01,
        RISING_EDGE = 0b10,
        NO_EDGE = 0b00
    } EdgeType_t;

    EdgeType_t ClassifyEdge(uint32_t sample, uint16_t bit_position);
    uint16_t ReadBit(uint32_t sample, uint16_t bit_position);

};

#endif /* _ADS_B_DECODER_HH_ */