#include "ads_b_decoder.hh"
#include "string.h"
#include <stdio.h> // for printing and popcount
// #include <bit> // bit operations for popcount

#define MIN(a,b) (((a)<(b))?(a):(b))
#define MAX(a,b) (((a)>(b))?(a):(b))
#define BITS_PER_WORD 32
#define BYTES_PER_WORD 4
// #define FALLING_EDGE 0b01
// #define RISING_EDGE 0b10

// TODO: change all operations to 32-bit? https://stackoverflow.com/a/71231277

/**
 * @brief Constructor.
*/
ADSBDecoder::ADSBDecoder() {
    ClearRxQueue();
}

/**
 * @brief Resets the rx queue.
*/
void ADSBDecoder::ClearRxQueue() {
    memset(rx_queue_, 0xFF, (kRxQueueMaxLenWords + 1)*BYTES_PER_WORD); // Clear out the RX queue array.
    rx_queue_front_ = 0;
    rx_queue_rear_ = 0;
    rx_queue_bit_offset_ = 0;
    rx_queue_len_bits_ = 0;
}

/**
 * @brief Adds a 32-bit word to the end of the rx queue.
 * @param[in] word Word to push onto the rx queue.
 * @retval True if push succeeded, false if the queue is full.
*/
bool ADSBDecoder::PushWord(uint32_t word) {
    if (rx_queue_len_bits_ >= kRxQueueMaxLenWords * BITS_PER_WORD) {
        return false; // not enough room for a new word
    }
    rx_queue_len_bits_ += BITS_PER_WORD;
    rx_queue_[rx_queue_rear_] = word; // rear points to a blank space ready to be written to
    rx_queue_rear_ = (rx_queue_rear_ + 1) % kRxQueueMaxLenWords;
    return true;
}
/**
 * @brief Pops a specified number of bits from the rx queue.
 * @param[in] num_bits Number of bits to pop (up to 32).
 * @param[out] buffer Buffer to write bits into. LSB is oldest bit.
 * @retval Number of bits popped successfully. May be less than num_bits if queue does not have enough readable bits.
*/
uint16_t ADSBDecoder::PopBits(uint16_t num_bits, uint32_t &buffer) {
    uint16_t num_bits_out = PeekBits(num_bits, buffer);
    rx_queue_bit_offset_ = rx_queue_bit_offset_ + num_bits_out; // nibbled num_bits_out off the front
    // Increment rx_queue_front_ by number of whole words eaten, then loop around if necessary.
    rx_queue_front_ = (rx_queue_front_ + (rx_queue_bit_offset_ / BITS_PER_WORD)) % kRxQueueMaxLenWords;
    rx_queue_bit_offset_ %= BITS_PER_WORD; // loop bit offset if necessary
    rx_queue_len_bits_ -= num_bits_out;
    return num_bits_out;
}

/**
 * @brief Reads the specified number of bits from the rx queue (does not remove them).
 * @param[in] num_bits Number of bits to read (up to 32).
 * @param[out] buffer Buffer to write bits into. LSB is oldest bit.
 * @retval Number of bits read successfully. May be less than num_bits if queue does not have enough readable bits.
*/
uint16_t ADSBDecoder::PeekBits(uint16_t num_bits, uint32_t &buffer) {
    num_bits = MIN(num_bits, BITS_PER_WORD); // ceiling is 32 bits read at once
    num_bits = MIN(num_bits, rx_queue_len_bits_); // can only read what's there

    // Retrieve a full 32 bits from the queue.
    buffer = (rx_queue_[rx_queue_front_] >> rx_queue_bit_offset_); // MSb's of oldest word.
    if (rx_queue_bit_offset_) {
        // Guard against left shift overflow if rx_queue_bit_offset_ is 0.
        buffer |=   (
                        rx_queue_[(rx_queue_front_ + 1) % kRxQueueMaxLenWords]
                        << (BITS_PER_WORD - rx_queue_bit_offset_)
                    ); // LSb's of second-oldest word.
    }
    
    // Mask off just the bottom num_bits.
    buffer &= (0xFFFFFFFF >> (BITS_PER_WORD-num_bits));
    return num_bits;
}

/**
 * @brief Returns the current length of the rx queue, in bits.
 * @retval Length of the rx queue in bits.
*/
uint16_t ADSBDecoder::GetRxQueueLenBits() {
    return rx_queue_len_bits_;
}

/**
 * @brief Classifies an edge at a given position in a bit buffer.
 * @param[in] sample 32-bit bit sample to check for an edge.
 * @param[in] bit_position bit position of oldest bit (LSb) in edge.
*/
ADSBDecoder::EdgeType_t ADSBDecoder::ClassifyEdge(uint32_t sample, uint16_t bit_position) {
    switch ((sample >> bit_position) & 0b11) {
        case 0b01: return FALLING_EDGE;
        case 0b10: return RISING_EDGE;
        default: return NO_EDGE;
    }
}



bool ADSBDecoder::FindPreamble() {
    while (rx_queue_len_bits_ > mf_template_preamble_len_bits) {
        uint32_t sample;
        if (PeekBits(mf_template_preamble_len_bits, sample) != mf_template_preamble_len_bits) {
            printf("ADSBDecoder::FindPreamble: Error while attempting to peek %d bits.\r\n", mf_template_preamble_len_bits);
        }
        int mf_correlation =    mf_coeff_11 * __builtin_popcount(sample & mf_template_preamble)
                            +   mf_coeff_10 * __builtin_popcount(sample & ~mf_template_preamble)
                            +   mf_coeff_01 * __builtin_popcount(~sample & mf_template_preamble)
                            +   mf_coeff_00 * __builtin_popcount(~sample & ~mf_template_preamble);
        if (mf_correlation >= mf_ok_threshold) {
            // Found preamble! Now verify.
            if (// TODO: finish this
                ClassifyEdge(sample, 1) == FALLING_EDGE
                && ClassifyEdge(sample, 3) == RISING_EDGE
                && ClassifyEdge(sample, 5) == FALLING_EDGE
            ) {

            }

            return true;
        }
        // Did not find preamble. Pop a bit and look again.
        if(PopBits(1, sample) != 1) {
            printf("ADSBDecoder::FindPreamble: Error while popping bit.\r\n");
        }
    }
    return false;
}