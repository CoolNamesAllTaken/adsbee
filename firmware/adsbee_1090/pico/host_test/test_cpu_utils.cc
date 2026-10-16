#include "cpu_utils.hh"
#include "gtest/gtest.h"
#include "hal_god_powers.hh"

TEST(CPUMonitor, UsagePercentFromIdleDelta) {
    EXPECT_EQ(CPUMonitor::UsagePercentFromIdleDelta(0, 0), 0);  // No time elapsed.
    EXPECT_EQ(CPUMonitor::UsagePercentFromIdleDelta(1000000, 1000000), 0);
    EXPECT_EQ(CPUMonitor::UsagePercentFromIdleDelta(0, 1000000), 100);
    EXPECT_EQ(CPUMonitor::UsagePercentFromIdleDelta(250000, 1000000), 75);
    // Idle can read slightly above total when the two counters are sampled at different instants.
    EXPECT_EQ(CPUMonitor::UsagePercentFromIdleDelta(1000100, 1000000), 0);
}

TEST(CPUMonitor, UsagePercentFromIdleDeltaLargeCounters) {
    // 100 * idle overflows 32 bits after ~43 s of 1 MHz ticks; a long mostly idle interval must still read low.
    EXPECT_EQ(CPUMonitor::UsagePercentFromIdleDelta(3000000000u, 3100000000u), 4);
}

TEST(CPUMonitor, UsagePercentFromIdleDeltaAcrossCounterWrap) {
    // Deltas taken with unsigned subtraction across a 32-bit wrap of the run time counter.
    uint32_t last_total = 0xFFFF0000u, last_idle = 0xFFFE0000u;
    uint32_t total = last_total + 1000000u, idle = last_idle + 900000u;  // Both wrap past zero.
    EXPECT_EQ(CPUMonitor::UsagePercentFromIdleDelta(idle - last_idle, total - last_total), 10);
}

TEST(CPUMonitor, UsagePercentFromBusyDelta) {
    EXPECT_EQ(CPUMonitor::UsagePercentFromBusyDelta(0, 0), 0);  // No time elapsed.
    EXPECT_EQ(CPUMonitor::UsagePercentFromBusyDelta(0, 1000000), 0);
    EXPECT_EQ(CPUMonitor::UsagePercentFromBusyDelta(1000000, 1000000), 100);
    EXPECT_EQ(CPUMonitor::UsagePercentFromBusyDelta(123000, 1000000), 12);
    EXPECT_EQ(CPUMonitor::UsagePercentFromBusyDelta(1000100, 1000000), 100);  // Clock sampling skew.
    EXPECT_EQ(CPUMonitor::UsagePercentFromBusyDelta(3000000000u, 3100000000u), 96);
}

#ifndef ON_ESP32
// RP2040 / CC1312 loop-tick estimator: 100e3 ticks per second is idle (0%), 100 ticks per second or fewer is 100%.
TEST(CPUMonitor, LoopTickUsage) {
    CPUMonitor monitor({.idle_ticks_per_update_interval = 100000, .full_usage_update_frequency_hz = 100,
                        .update_interval_ms = 1000});
    set_time_since_boot_ms(0);
    monitor.Update();  // Starts the first interval.

    auto run_interval = [&](uint32_t ticks) {
        for (uint32_t i = 0; i < ticks; i++) monitor.Tick();
        inc_time_since_boot_ms(1000);
        monitor.Update();
        return monitor.GetUsagePercent();
    };
    EXPECT_EQ(run_interval(100000 + 100), 0);  // Idle loop.
    EXPECT_EQ(run_interval(50000 + 100), 50);
    EXPECT_EQ(run_interval(100), 100);  // Exactly the full usage rate.
    // A loop slower than the full usage rate reads 100%, not an underflowed 0%.
    EXPECT_EQ(run_interval(50), 100);
    EXPECT_EQ(run_interval(0), 100);
}
#endif

#ifndef ON_ESP32
class CPUMonitorBusyTime : public ::testing::Test {
   protected:
    void SetUp() override {
        set_time_since_boot_ms(0);
        monitor.Update();  // Starts the first interval.
    }

    // One loop pass of pass_us timed as a work region, with an interrupt of isr_us in the middle.
    void Pass(uint32_t pass_us, bool did_work, uint32_t isr_us = 0) {
        monitor.BeginWork();
        inc_time_since_boot_us((pass_us - isr_us) / 2);
        if (isr_us > 0) {
            monitor.OnISREnter();
            inc_time_since_boot_us(isr_us);
            monitor.OnISRExit();
        }
        inc_time_since_boot_us(pass_us - isr_us - (pass_us - isr_us) / 2);
        monitor.EndWork(did_work);
    }

    // Runs idle passes to the end of a 1 s interval that began at interval_start_us and returns the usage.
    uint8_t FinishInterval(uint64_t interval_start_us) {
        uint64_t end_us = interval_start_us + 1000000;
        while (get_time_since_boot_us() + 10 <= end_us) Pass(10, false);
        set_time_since_boot_us(end_us);
        EXPECT_TRUE(monitor.Update());
        return monitor.GetUsagePercent();
    }

    CPUMonitor monitor = CPUMonitor({.update_interval_ms = 1000, .use_busy_time = true});
};

TEST_F(CPUMonitorBusyTime, IdlePassesReadZero) {
    for (uint32_t i = 0; i < 2000000; i++) monitor.Tick();  // Ignored in busy time mode.
    EXPECT_EQ(FinishInterval(0), 0);
}

TEST_F(CPUMonitorBusyTime, WorkPasses) {
    for (int i = 0; i < 250; i++) Pass(1000, true);
    EXPECT_EQ(FinishInterval(0), 25);
    for (int i = 0; i < 1000; i++) Pass(1000, true);
    EXPECT_EQ(FinishInterval(1000000), 100);
}

TEST_F(CPUMonitorBusyTime, InterruptInWorkPassCountedOnce) {
    for (int i = 0; i < 100; i++) Pass(1000, true, 400);
    EXPECT_EQ(FinishInterval(0), 10);
}

TEST_F(CPUMonitorBusyTime, InterruptInIdlePassCounted) {
    for (int i = 0; i < 100; i++) Pass(1000, false, 300);
    EXPECT_EQ(FinishInterval(0), 3);
}

TEST_F(CPUMonitorBusyTime, NestedWorkScopesCountedOnce) {
    {
        CPUMonitor::WorkScope outer(monitor);
        inc_time_since_boot_us(100000);
        {
            CPUMonitor::WorkScope inner(monitor);
            inc_time_since_boot_us(100000);
            monitor.OnISREnter();
            inc_time_since_boot_us(50000);
            monitor.OnISRExit();
        }
        inc_time_since_boot_us(100000);
    }
    inc_time_since_boot_us(200000);  // Outside any region: not counted.
    EXPECT_EQ(FinishInterval(0), 35);
}

TEST_F(CPUMonitorBusyTime, NestedInterruptsCountedOnce) {
    monitor.OnISREnter();
    inc_time_since_boot_us(100000);
    monitor.OnISREnter();
    inc_time_since_boot_us(100000);
    monitor.OnISRExit();
    inc_time_since_boot_us(100000);
    monitor.OnISRExit();
    EXPECT_EQ(FinishInterval(0), 30);
}

TEST_F(CPUMonitorBusyTime, PartialIntervalCarriesOver) {
    for (int i = 0; i < 30; i++) Pass(1000, true);
    EXPECT_EQ(FinishInterval(0), 3);
    // Not yet an interval: keeps the last value, and the work counts toward the next one.
    Pass(400000, true);
    EXPECT_FALSE(monitor.Update());
    EXPECT_EQ(monitor.GetUsagePercent(), 3);
    EXPECT_EQ(FinishInterval(1000000), 40);
}

TEST_F(CPUMonitorBusyTime, MicrosecondClockWrap) {
    // The 32 bit microsecond clock wraps every ~71.6 minutes: start an interval just before a wrap.
    uint64_t start_us = (1ull << 32) - 500000;
    set_time_since_boot_us(start_us);
    monitor.Update();
    Pass(200000, true, 50000);                // Ends before the wrap.
    Pass(600000, false, 60000);               // Spans the wrap.
    Pass(100000, true, 20000);                // After the wrap.
    EXPECT_EQ(FinishInterval(start_us), 36);  // 200 + 60 + 100 ms.
}

TEST_F(CPUMonitorBusyTime, CounterWrap) {
    // A work counter close to its wrap: one interval of 4294.767 s, fully busy.
    Pass(0xFFFFFFFFu - 199999u, true);
    set_time_since_boot_us(4294767000ull);
    EXPECT_TRUE(monitor.Update());
    EXPECT_EQ(monitor.GetUsagePercent(), 100);
    Pass(500000, true);  // Wraps the counter.
    EXPECT_EQ(FinishInterval(4294767000ull), 50);
}
#endif
