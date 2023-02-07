#ifndef _ADS_B_DECODER_HH_
#define _ADS_B_DECODER_HH_

#include <stdint.h>

class ADSBDecoder {
public:
    static const uint16_t kRxQueueMaxLenWords = 10; // [Words] Length of received bits buffer.

    // Preamble detection matched filter coefficients.
    int mf_coeff_11 = 1; // Matched filter coefficient for template bit = 1, message bit = 1.
    int mf_coeff_10 = -4; // Matched filter coefficient for template bit = 1, message bit = 0.
    int mf_coeff_01 = -4; // Matched filter coefficient for template bit = 0, message bit = 1.
    int mf_coeff_00 = 1; // Matched filter coefficient for template bit = 0, message bit = 0.
    int mf_ok_threshold = 5; // Threshold for determining a filter match.

    ADSBDecoder(); // constructor

    void ClearRxQueue();
    bool PushWord(uint32_t word); // Pushes a full word onto the rx queue. Returns True if the queue had space.
    uint16_t PopBits(uint16_t num_bits, uint32_t &buffer);
    uint16_t PeekBits(uint16_t num_bits, uint32_t &buffer);
    uint16_t GetRxQueueLenBits();

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

};

#endif /* _ADS_B_DECODER_HH_ */