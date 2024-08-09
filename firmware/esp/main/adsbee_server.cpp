#include "adsbee_server.hh"

#include "esp_log.h"

bool IngestSPIPacket(uint8_t *buf, uint16_t buf_len_bytes) {
    uint16_t min_sc_message_length = sizeof(SPICoprocessor::SCMessage);
    if (buf_len_bytes < min_sc_message_length) {
        ESP_LOGI("IngestSPIPacket", "Can't pull a valid SCMessage from a %d Byte message. Minimum length is %d Bytes.",
                 buf_len_bytes, min_sc_message_length);
        return false;
    }
    // switch (buf[0]): {
    //     case SPICoprocessor::PacketType::kSCPacketTypeSettings:
    //         break;
    //     cast SPICoprocessor::PacketType::k
    // }
    return true;
}