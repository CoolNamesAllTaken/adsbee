    #ifndef _BUFFER_UTILS_HH_
    #define _BUFFER_UTILS_HH_

    #include <cstdint>

    void print_binary_32(uint32_t); // for debugging
    
    uint32_t get_24_bit_word_from_buffer(uint32_t first_bit_index, uint32_t buffer[]);
    uint32_t get_n_bit_word_from_buffer(uint16_t n, uint32_t first_bit_index, uint32_t buffer[]);
    void set_n_bit_word_in_buffer(uint16_t n, uint32_t word, uint32_t first_bit_index, uint32_t buffer[]);

    #endif /* _BUFFER_UTILS_HH_ */