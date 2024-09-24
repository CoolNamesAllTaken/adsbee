#include "gdl90_utils.hh"
#include "gtest/gtest.h"

TEST(GDL90Utils, TestWriteBufferWithEscapes) {
    uint8_t to_buf[kGDL90MessageMaxLenBytes];

    // These examples are from page 5 of the GDL90 spec below:
    // https://www.faa.gov/sites/faa.gov/files/air_traffic/technology/adsb/archival/GDL90_Public_ICD_RevA.PDF

    // Start of message ID #2 with second byte 0x7E.
    // Omit actual start of message flag since that doesn't get passed to WriteBuffer.
    uint8_t from_buf_0[] = {0x02, 0x7E, 0x05};
    uint16_t from_buf_0_len_bytes = 3;
    EXPECT_EQ(4, WriteBufferWithGDL90Escapes(to_buf, from_buf_0, from_buf_0_len_bytes));
    EXPECT_EQ(to_buf[0], 0x02);
    EXPECT_EQ(to_buf[1], 0x7D);
    EXPECT_EQ(to_buf[2], 0x5E);
    EXPECT_EQ(to_buf[3], 0x05);

    // Start of message ID #3 with second byte 0x7D.
    // Omit actual start of message flag since that doesn't get passed to WriteBuffer.
    uint8_t from_buf_1[] = {0x03, 0x7D, 0x06};
    uint16_t from_buf_1_len_bytes = 3;
    EXPECT_EQ(4, WriteBufferWithGDL90Escapes(to_buf, from_buf_1, from_buf_1_len_bytes));
    EXPECT_EQ(to_buf[0], 0x03);
    EXPECT_EQ(to_buf[1], 0x7D);
    EXPECT_EQ(to_buf[2], 0x5D);
    EXPECT_EQ(to_buf[3], 0x06);

    // End of message with CRC value of 0x7D 0x7E.
    // Omit end of message flag since that doesn't get passed to the WriteBuffer function.
    uint8_t from_buf_2[] = {0x01, 0x09, 0x10, 0x7D, 0x7E};
    uint16_t from_buf_2_len_bytes = 5;
    EXPECT_EQ(7, WriteBufferWithGDL90Escapes(to_buf, from_buf_2, from_buf_2_len_bytes));
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