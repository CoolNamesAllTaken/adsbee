#include "ads_b_decoder.hh"
#include "string.h"

#define MIN(a,b) (((a)<(b))?(a):(b))
#define MAX(a,b) (((a)>(b))?(a):(b))
#define BITS_PER_WORD 32
#define BYTES_PER_WORD 4

// TODO: change all operations to 32-bit? https://stackoverflow.com/a/71231277

ADSBDecoder::ADSBDecoder() {
    ClearRxQueue();
}

void ADSBDecoder::ClearRxQueue() {
    memset(rx_queue_, 0xFF, (kRxQueueMaxLenWords + 1)*BYTES_PER_WORD); // Clear out the RX queue array.
    rx_queue_front_ = 0;
    rx_queue_rear_ = 0;
    rx_queue_bit_offset_ = 0;
    rx_queue_len_bits_ = 0;
}

bool ADSBDecoder::PushWord(uint32_t word) {
    if (rx_queue_len_bits_ > kRxQueueMaxLenWords * BITS_PER_WORD) {
        return false; // not enough room for a new word
    }
    rx_queue_len_bits_ += BITS_PER_WORD;
    rx_queue_[rx_queue_rear_] = word; // rear points to a blank space ready to be written to
    rx_queue_rear_ = (rx_queue_rear_ + 1) % kRxQueueMaxLenWords;
    return true;
}

// inline uint16_t IncrementQueueIndex(uint16_t index, int increment, uint16_t queue_len) {
//     return (index + increment) % queue_len;
// }

/**
 * @brief Pops a specified number of bits from the rx queue.
 * @param[in] num_bits Number of bits to pop (up to 32).
 * @param[out] buffer Buffer to write bits into. LSB is oldest bit.
 * @retval Number of bits popped successfully.
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