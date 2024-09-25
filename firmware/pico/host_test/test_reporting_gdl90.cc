#include "gdl90_utils.hh"
#include "gtest/gtest.h"

GDL90Reporter gdl90;

TEST(GDL90Utils, TestWriteBufferWithEscapes) {
    uint8_t to_buf[GDL90Reporter::kGDL90MessageMaxLenBytes];

    // These examples are from page 5 of the GDL90 spec below:
    // https://www.faa.gov/sites/faa.gov/files/air_traffic/technology/adsb/archival/GDL90_Public_ICD_RevA.PDF

    // Start of message ID #2 with second byte 0x7E.
    // Omit actual start of message flag since that doesn't get passed to WriteBuffer.
    uint8_t from_buf_0[] = {0x02, 0x7E, 0x05};
    uint16_t from_buf_0_len_bytes = 3;
    ASSERT_EQ(4, gdl90.WriteBufferWithGDL90Escapes(to_buf, from_buf_0, from_buf_0_len_bytes));
    EXPECT_EQ(to_buf[0], 0x02);
    EXPECT_EQ(to_buf[1], 0x7D);
    EXPECT_EQ(to_buf[2], 0x5E);
    EXPECT_EQ(to_buf[3], 0x05);

    // Start of message ID #3 with second byte 0x7D.
    // Omit actual start of message flag since that doesn't get passed to WriteBuffer.
    uint8_t from_buf_1[] = {0x03, 0x7D, 0x06};
    uint16_t from_buf_1_len_bytes = 3;
    ASSERT_EQ(4, gdl90.WriteBufferWithGDL90Escapes(to_buf, from_buf_1, from_buf_1_len_bytes));
    EXPECT_EQ(to_buf[0], 0x03);
    EXPECT_EQ(to_buf[1], 0x7D);
    EXPECT_EQ(to_buf[2], 0x5D);
    EXPECT_EQ(to_buf[3], 0x06);

    // End of message with CRC value of 0x7D 0x7E.
    // Omit end of message flag since that doesn't get passed to the WriteBuffer function.
    uint8_t from_buf_2[] = {0x01, 0x09, 0x10, 0x7D, 0x7E};
    uint16_t from_buf_2_len_bytes = 5;
    ASSERT_EQ(7, gdl90.WriteBufferWithGDL90Escapes(to_buf, from_buf_2, from_buf_2_len_bytes));
    EXPECT_EQ(to_buf[0], 0x01);
    EXPECT_EQ(to_buf[1], 0x09);
    EXPECT_EQ(to_buf[2], 0x10);
    EXPECT_EQ(to_buf[3], 0x7D);
    EXPECT_EQ(to_buf[4], 0x5D);
    EXPECT_EQ(to_buf[5], 0x7D);
    EXPECT_EQ(to_buf[6], 0x5E);
}

void crc_init(uint16_t crc16_table[]) {
    unsigned int i, bitctr, crc;
    for (i = 0; i < 256; i++) {
        crc = (i << 8);
        for (bitctr = 0; bitctr < 8; bitctr++) {
            crc = (crc << 1) ^ ((crc & 0x8000) ? 0x1021 : 0);
        }
        crc16_table[i] = crc;
    }
}

TEST(GDL90Utils, PrintCRCTable) {
    uint16_t crc16_table[256];
    crc_init(crc16_table);
    printf("uint16_t crc16_table[256] = {");
    for (uint16_t i = 0; i < 256; i++) {
        printf("0x%x%s", crc16_table[i], i < 255 ? ", " : "};\r\n");
    }
}

TEST(GDL90Utils, CalcCRC16) {
    // 0x7E 0x00 0x81 0x41 0xDB 0xD0 0x08 0x02 0xB3 0x8B 0x7E
    uint8_t unescaped_message[] = {0x00, 0x81, 0x41, 0xDB, 0xD0, 0x08, 0x02};
    ASSERT_EQ(0x8BB3, gdl90.CalculateGDL90CRC16(unescaped_message, 7));

    uint8_t crc_unescaped[] = {0xB3, 0x8B};  // LSB first.
    uint8_t crc_escaped[4];
    ASSERT_EQ(2, gdl90.WriteBufferWithGDL90Escapes(crc_escaped, crc_unescaped, 2));
    EXPECT_EQ(crc_escaped[0], 0xB3);
    EXPECT_EQ(crc_escaped[1], 0x8B);
}

TEST(GDL90Utils, WriteGDL90Message) {
    // 0x7E 0x00 0x81 0x41 0xDB 0xD0 0x08 0x02 0xB3 0x8B 0x7E
    uint8_t buf[GDL90Reporter::kGDL90MessageMaxLenBytes];
    memset(buf, 0xFF, GDL90Reporter::kGDL90MessageMaxLenBytes);  // For easier debugging.
    uint8_t unescaped_message[] = {0x00, 0x81, 0x41, 0xDB, 0xD0, 0x08, 0x02};
    ASSERT_EQ(11, gdl90.WriteGDL90Message(buf, unescaped_message, sizeof(unescaped_message)));
    EXPECT_EQ(buf[0], 0x7E);
    EXPECT_EQ(buf[1], 0x00);
    EXPECT_EQ(buf[2], 0x81);
    EXPECT_EQ(buf[3], 0x41);
    EXPECT_EQ(buf[4], 0xDB);
    EXPECT_EQ(buf[5], 0xD0);
    EXPECT_EQ(buf[6], 0x08);
    EXPECT_EQ(buf[7], 0x02);
    EXPECT_EQ(buf[8], 0xB3);
    EXPECT_EQ(buf[9], 0x8B);
    EXPECT_EQ(buf[10], 0x7E);
}

TEST(GDL90Utils, HeartBeatMessage) {
    // 0x7E 0x00 0x81 0x41 0xDB 0xD0 0x08 0x02 0xB3 0x8B 0x7E
    uint8_t buf[GDL90Reporter::kGDL90MessageMaxLenBytes];
    // Set Status Byte 1 = 0b10000001.
    gdl90.gnss_position_valid = true;
    gdl90.maintenance_required = false;
    gdl90.csa_requested = true;
    gdl90.csa_not_available = false;
    // Set Status Byte 2 = 0b01000001.
    gdl90.utc_timing_is_valid = true;
    // Timestamp must have MS bit = 0b0.
    uint32_t timestamp = (0b0 << 16) | 0xD0DB;  // Set timestamp to match sample message.
    uint16_t message_counts = 0x0208;
    ASSERT_EQ(11, gdl90.WriteGDL90HeartbeatMessage(buf, timestamp, message_counts));
    EXPECT_EQ(buf[0], 0x7E);
    EXPECT_EQ(buf[1], 0x00);
    EXPECT_EQ(buf[2], 0x81);
    EXPECT_EQ(buf[3], 0x41);
    EXPECT_EQ(buf[4], 0xDB);
    EXPECT_EQ(buf[5], 0xD0);
    EXPECT_EQ(buf[6], 0x08);
    EXPECT_EQ(buf[7], 0x02);
    EXPECT_EQ(buf[8], 0xB3);
    EXPECT_EQ(buf[9], 0x8B);
    EXPECT_EQ(buf[10], 0x7E);
}

TEST(GDL90Utils, InitMessage) {
    // TODO: Add tests here!
}

TEST(GDL90Utils, UplinkDataMessage) {
    // TODO: Add tests here!
}