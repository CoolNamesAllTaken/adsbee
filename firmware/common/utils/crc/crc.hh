#ifndef CRC_HH_
#define CRC_HH_

#include <cstdint>

uint32_t crc24(uint8_t *buffer, uint16_t buffer_len_bytes, uint32_t initial_value = 0x0);

#endif /* CRC_HH_ */