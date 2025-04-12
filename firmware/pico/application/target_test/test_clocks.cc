#include "adsbee.hh"
#include "hardware_unit_tests.hh"

UTEST(Clocks, Test48MHzMLATCounter) {
    uint64_t mlat_counter_start = adsbee.GetMLAT48MHzCounts();
    sleep_ms(1);
    // Expect MLAT counter to increment by at least 48000.
    uint64_t mlat_counter_end = adsbee.GetMLAT48MHzCounts();
    uint64_t mlat_counter_delta = mlat_counter_end - mlat_counter_start;
    EXPECT_NEAR(48'000, mlat_counter_delta, 4'000);
}