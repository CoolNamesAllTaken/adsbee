#include "adsbee.hh"
#include "hardware_unit_tests.hh"

UTEST(Clocks, Test48MHzMLATCounter) {
    static const uint32_t kTestNumRepeats = 5;
    for (uint32_t i = 0; i < kTestNumRepeats; i++) {
        uint64_t mlat_counter_start = adsbee.GetMLAT48MHzCounts();
        sleep_ms(1000);
        // Expect MLAT counter to increment by at least 48000.
        uint64_t mlat_counter_end = adsbee.GetMLAT48MHzCounts();
        uint64_t mlat_counter_delta = mlat_counter_end - mlat_counter_start;
        EXPECT_NEAR(48'000'000, mlat_counter_delta, 1200);
    }
}

UTEST(Clocks, Test12MHzMLATCounter) {
    static const uint32_t kTestNumRepeats = 5;
    for (uint32_t i = 0; i < kTestNumRepeats; i++) {
        uint64_t mlat_counter_start = adsbee.GetMLAT12MHzCounts();
        sleep_ms(1000);
        // Expect MLAT counter to increment by at least 12000.
        uint64_t mlat_counter_end = adsbee.GetMLAT12MHzCounts();
        uint64_t mlat_counter_delta = mlat_counter_end - mlat_counter_start;
        EXPECT_NEAR(12'000'000, mlat_counter_delta, 300);
    }
}

UTEST(Clocks, TestMLATJitterPWMSlice) {
    // Verify that the MLAT jitter PWM slice is running at 48MHz.
    static const uint32_t kTestNumRepeats = 10;
    for (uint32_t i = 0; i < kTestNumRepeats; i++) {
        uint16_t mlat_jitter_counts_start = adsbee.GetMLATJitterPWMSliceCounts();
        sleep_us(10);
        // Expect MLAT jitter PWM slice to increment by around 480 counts in 10us (48MHz).
        uint16_t mlat_jitter_counts_end = adsbee.GetMLATJitterPWMSliceCounts();
        uint16_t mlat_jitter_counts_delta = mlat_jitter_counts_end - mlat_jitter_counts_start;
        EXPECT_NEAR(480, mlat_jitter_counts_delta, 10);
    }
}