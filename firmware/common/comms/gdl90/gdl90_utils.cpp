#include "gdl90_utils.hh"

#include "comms.hh"

// Initialize static variables.
const uint16_t GDL90Reporter::kGDL90CRC16Table[] = {
    0x0,    0x1021, 0x2042, 0x3063, 0x4084, 0x50a5, 0x60c6, 0x70e7, 0x8108, 0x9129, 0xa14a, 0xb16b, 0xc18c, 0xd1ad,
    0xe1ce, 0xf1ef, 0x1231, 0x210,  0x3273, 0x2252, 0x52b5, 0x4294, 0x72f7, 0x62d6, 0x9339, 0x8318, 0xb37b, 0xa35a,
    0xd3bd, 0xc39c, 0xf3ff, 0xe3de, 0x2462, 0x3443, 0x420,  0x1401, 0x64e6, 0x74c7, 0x44a4, 0x5485, 0xa56a, 0xb54b,
    0x8528, 0x9509, 0xe5ee, 0xf5cf, 0xc5ac, 0xd58d, 0x3653, 0x2672, 0x1611, 0x630,  0x76d7, 0x66f6, 0x5695, 0x46b4,
    0xb75b, 0xa77a, 0x9719, 0x8738, 0xf7df, 0xe7fe, 0xd79d, 0xc7bc, 0x48c4, 0x58e5, 0x6886, 0x78a7, 0x840,  0x1861,
    0x2802, 0x3823, 0xc9cc, 0xd9ed, 0xe98e, 0xf9af, 0x8948, 0x9969, 0xa90a, 0xb92b, 0x5af5, 0x4ad4, 0x7ab7, 0x6a96,
    0x1a71, 0xa50,  0x3a33, 0x2a12, 0xdbfd, 0xcbdc, 0xfbbf, 0xeb9e, 0x9b79, 0x8b58, 0xbb3b, 0xab1a, 0x6ca6, 0x7c87,
    0x4ce4, 0x5cc5, 0x2c22, 0x3c03, 0xc60,  0x1c41, 0xedae, 0xfd8f, 0xcdec, 0xddcd, 0xad2a, 0xbd0b, 0x8d68, 0x9d49,
    0x7e97, 0x6eb6, 0x5ed5, 0x4ef4, 0x3e13, 0x2e32, 0x1e51, 0xe70,  0xff9f, 0xefbe, 0xdfdd, 0xcffc, 0xbf1b, 0xaf3a,
    0x9f59, 0x8f78, 0x9188, 0x81a9, 0xb1ca, 0xa1eb, 0xd10c, 0xc12d, 0xf14e, 0xe16f, 0x1080, 0xa1,   0x30c2, 0x20e3,
    0x5004, 0x4025, 0x7046, 0x6067, 0x83b9, 0x9398, 0xa3fb, 0xb3da, 0xc33d, 0xd31c, 0xe37f, 0xf35e, 0x2b1,  0x1290,
    0x22f3, 0x32d2, 0x4235, 0x5214, 0x6277, 0x7256, 0xb5ea, 0xa5cb, 0x95a8, 0x8589, 0xf56e, 0xe54f, 0xd52c, 0xc50d,
    0x34e2, 0x24c3, 0x14a0, 0x481,  0x7466, 0x6447, 0x5424, 0x4405, 0xa7db, 0xb7fa, 0x8799, 0x97b8, 0xe75f, 0xf77e,
    0xc71d, 0xd73c, 0x26d3, 0x36f2, 0x691,  0x16b0, 0x6657, 0x7676, 0x4615, 0x5634, 0xd94c, 0xc96d, 0xf90e, 0xe92f,
    0x99c8, 0x89e9, 0xb98a, 0xa9ab, 0x5844, 0x4865, 0x7806, 0x6827, 0x18c0, 0x8e1,  0x3882, 0x28a3, 0xcb7d, 0xdb5c,
    0xeb3f, 0xfb1e, 0x8bf9, 0x9bd8, 0xabbb, 0xbb9a, 0x4a75, 0x5a54, 0x6a37, 0x7a16, 0xaf1,  0x1ad0, 0x2ab3, 0x3a92,
    0xfd2e, 0xed0f, 0xdd6c, 0xcd4d, 0xbdaa, 0xad8b, 0x9de8, 0x8dc9, 0x7c26, 0x6c07, 0x5c64, 0x4c45, 0x3ca2, 0x2c83,
    0x1ce0, 0xcc1,  0xef1f, 0xff3e, 0xcf5d, 0xdf7c, 0xaf9b, 0xbfba, 0x8fd9, 0x9ff8, 0x6e17, 0x7e36, 0x4e55, 0x5e74,
    0x2e93, 0x3eb2, 0xed1,  0x1ef0};

uint16_t GDL90Reporter::WriteGDL90Message(uint8_t *to_buf, uint8_t *unescaped_message,
                                          uint8_t unescaped_message_len_bytes) {
    uint16_t bytes_written = 0;
    to_buf[bytes_written++] = kGDL90FlagByte;  // Beginning flag byte.
    bytes_written +=
        WriteBufferWithGDL90Escapes(to_buf + bytes_written, unescaped_message, unescaped_message_len_bytes);
    // Calculate the CRC with unescaped message ID and data.
    uint16_t crc = CalculateGDL90CRC16(unescaped_message, unescaped_message_len_bytes);
    uint8_t crc_buf[sizeof(crc)] = {static_cast<uint8_t>(crc & 0xFF), static_cast<uint8_t>(crc >> 8)};  // LSB first.
    bytes_written += WriteBufferWithGDL90Escapes(to_buf + bytes_written, crc_buf, sizeof(crc));
    to_buf[bytes_written++] = kGDL90FlagByte;  // Ending flag byte.
    return bytes_written;
}

uint16_t GDL90Reporter::WriteBufferWithGDL90Escapes(uint8_t *to_buf, const uint8_t *from_buf,
                                                    uint16_t from_buf_num_bytes) {
    uint16_t to_buf_num_bytes = 0;
    for (uint16_t i = 0; i < from_buf_num_bytes; i++) {
        if (from_buf[i] == kGDL90FlagByte || from_buf[i] == kGDL90ControlEscapeChar) {
            // Escape any occurrence of 0x7E and 0x7D.
            to_buf[to_buf_num_bytes++] = kGDL90ControlEscapeChar;
            to_buf[to_buf_num_bytes++] = from_buf[i] ^ 0x20;
        } else {
            // Write other values as normal.
            to_buf[to_buf_num_bytes++] = from_buf[i];
        }
    }
    return to_buf_num_bytes;
}

uint16_t GDL90Reporter::WriteGDL90HeartbeatMessage(uint8_t *to_buf, uint32_t timestamp_sec_since_0000z,
                                                   uint16_t message_counts) {
    const uint16_t kMessageBufLenBytes = 7;
    uint8_t message_buf[kMessageBufLenBytes];
    // 1: Message ID
    message_buf[0] = kGDL90MessageIDHeartbeat;
    // 2: Status Byte 1
    message_buf[1] = (gnss_position_valid << 7)  // GPS Position Valid: Set valid when ownship GPS position available.
                     | (maintenance_required << 6)  // Maintenance Required: Set to 1 if indicating an error.
                     | uat_initialized;             // UAT Initialized: always set to 1.
    // 3: Status Byte 2
    message_buf[2] = (timestamp_sec_since_0000z >> 16) << 7  // Timestamp MS bit.
                     | (csa_requested << 6)                  // 1 = Conflict Situational Awareness has been requested.
                     | (csa_not_available << 5)  // 1 = Conflict Situational Awareness not available at this time.
                     | utc_timing_is_valid;      // 1 = UTC timing is valid.
    // 4-5: Timestamp
    message_buf[3] = timestamp_sec_since_0000z & 0xFF;         // Timestamp LSB.
    message_buf[4] = (timestamp_sec_since_0000z >> 8) & 0xFF;  // Timestamp MSB (missing MS bit).
    // 6-7: Message Counts
    message_counts = MIN(1023, message_counts);
    message_buf[5] = message_counts & 0xFF;
    message_buf[6] = message_counts >> 8;
    return WriteGDL90Message(to_buf, message_buf, kMessageBufLenBytes);
}

uint16_t GDL90Reporter::WriteGDL90InitMessage(uint8_t *to_buf) {
    const uint16_t kMessageBufLenBytes = 3;
    uint8_t message_buf[kMessageBufLenBytes];
    // 1: Message ID
    message_buf[0] = kGDL90MessageIDInitialization;
    // 2: Configuration Byte 1
    message_buf[1] = (audio_test << 6)       // 1 = Initiate audio test.
                     | (audio_inhibit << 1)  // 1 = Suppress GDL90 audio output.
                     | cdti_ok;              // 1 = Cockpit Traffic Display (CDTI) capability is operating.
    // 3: Configuration Byte 2
    message_buf[2] = (csa_audio_disable << 1)  // 1 = Disable GDL90 audible traffic alerts.
                     | csa_disable;            // 1 = Disable CSA traffic alerting.
    return WriteGDL90Message(to_buf, message_buf, kMessageBufLenBytes);
}

uint16_t GDL90Reporter::WriteGDL90UplinkDataMessage(uint8_t *to_buf, uint8_t *uplink_payload,
                                                    uint16_t uplink_payload_len_bytes, uint32_t tor_us) {
    // Time of Arrival (TOR) = 24-bit value with resolution of 80ns. Valid range is 0 to 1 sec (0-12499999).
    uint32_t tor = 0xFFFFFF;  // Default value: insufficient timing accuracy to say what the time of arrival is.
    if (tor_us != 0xFFFFFFFF) {
        tor = tor_us * 1000 / 80;  // Convert us tor to fractional value with resolution of 80ns.
    }
    if (uplink_payload_len_bytes > kGDL90MessageMaxLenBytes) {
        CONSOLE_ERROR("GDL90Reporter::WriteGDL90UplinkDataMessage",
                      "Received uplink payload of length %d bytes, maximum is %d Bytes (should actually be smaller to "
                      "account for potential escaping).",
                      uplink_payload_len_bytes, kGDL90MessageMaxLenBytes);
        return 0;
    }
    const uint16_t kMessageBufLenBytes = sizeof(GDL90MessageID) + 3 + uplink_payload_len_bytes;
    uint8_t message_buf[kMessageBufLenBytes];
    message_buf[0] = kGDL90MessageIDUplinkData;
    message_buf[1] = tor & 0xFF;
    message_buf[2] = (tor >> 8) & 0xFF;
    message_buf[3] = (tor >> 16) & 0xFF;
    memcpy(message_buf + sizeof(GDL90MessageID) + 3, uplink_payload, uplink_payload_len_bytes);
    return WriteGDL90Message(to_buf, message_buf, kMessageBufLenBytes);
}

uint16_t GDL90Reporter::WriteGDL90TargetReportMessage(uint8_t *to_buf, const GDL90TargetReportData &data,
                                                      bool ownship) {
    const uint16_t kMessageBufLenBytes = 28;
    uint8_t message_buf[kMessageBufLenBytes];
    message_buf[0] = ownship ? kGDL90MessageIDOwnshipReport : kGDL90MessageIDTrafficReport;
    // TODO: fill in the rest of the message!
    return WriteGDL90Message(to_buf, message_buf, kMessageBufLenBytes);
}