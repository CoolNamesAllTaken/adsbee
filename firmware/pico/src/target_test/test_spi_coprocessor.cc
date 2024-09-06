#include "hardware_unit_tests.hh"
#include "spi_coprocessor.hh"

UTEST(SpiCoprocessor, WriteReadScratchNoAck) {
    uint32_t scratch_out = 0xDEADBEEF;
    EXPECT_TRUE(esp32.Write(SPICoprocessor::SCAddr::kAddrScratch, scratch_out));
    uint32_t scratch_in = 0x0;
    EXPECT_TRUE(esp32.Read(SPICoprocessor::SCAddr::kAddrScratch, scratch_in));
    EXPECT_EQ(scratch_out, scratch_in);
}

UTEST(SpiCoprocessor, WriteReadScratchWithAck) {
    uint32_t scratch_out = 0xDEADBEEF;
    // Write requires an ack.
    EXPECT_TRUE(esp32.Write(SPICoprocessor::SCAddr::kAddrScratch, scratch_out, true));
    uint32_t scratch_in = 0x0;
    EXPECT_TRUE(esp32.Read(SPICoprocessor::SCAddr::kAddrScratch, scratch_in));
    EXPECT_EQ(scratch_out, scratch_in);
}