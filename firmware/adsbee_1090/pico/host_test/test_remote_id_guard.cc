#include <cstring>

#include "gtest/gtest.h"
#include "remote_id_guard.hh"

static constexpr uint32_t kKB = 1024;

TEST(RemoteIDGuard, AllowedTransports) {
    // With PSRAM everything runs next to any network interface.
    EXPECT_EQ(RemoteIDGuard::AllowedTransports(true, true, true, true), RemoteIDGuard::kTransportsAll);
    // Without PSRAM: everything with no network, Bluetooth only next to Ethernet, nothing next to WiFi.
    EXPECT_EQ(RemoteIDGuard::AllowedTransports(false, false, false, false), RemoteIDGuard::kTransportsAll);
    EXPECT_EQ(RemoteIDGuard::AllowedTransports(false, false, false, true), RemoteIDGuard::kTransportsBLE);
    EXPECT_EQ(RemoteIDGuard::AllowedTransports(false, true, false, false), 0);
    EXPECT_EQ(RemoteIDGuard::AllowedTransports(false, false, true, false), 0);
    EXPECT_EQ(RemoteIDGuard::AllowedTransports(false, true, true, true), 0);
}

TEST(RemoteIDGuard, HeapBelowReserve) {
    EXPECT_FALSE(RemoteIDGuard::HeapBelowReserve(RemoteIDGuard::kReserveFreeBytes,
                                                 RemoteIDGuard::kReserveLargestBlockBytes));
    EXPECT_TRUE(RemoteIDGuard::HeapBelowReserve(RemoteIDGuard::kReserveFreeBytes - 1, 100 * kKB));
    EXPECT_TRUE(RemoteIDGuard::HeapBelowReserve(100 * kKB, RemoteIDGuard::kReserveLargestBlockBytes - 1));
}

TEST(RemoteIDGuard, HeapWatchPausesAndBacksOff) {
    RemoteIDGuard::HeapWatch watch;
    uint32_t t = 1000;
    // Healthy heap while running: no pause.
    EXPECT_FALSE(watch.Update(80 * kKB, 30 * kKB, t, true));
    // Low heap while not running: nothing to pause.
    EXPECT_FALSE(watch.Update(20 * kKB, 10 * kKB, t, false));

    // Low heap while running pauses for the hold-off, even once the heap recovers.
    EXPECT_TRUE(watch.Update(30 * kKB, 30 * kKB, t, true));
    EXPECT_EQ(watch.GetNumPauses(), 1);
    EXPECT_TRUE(watch.Update(110 * kKB, 40 * kKB, t + RemoteIDGuard::kResumeHoldOffMs - 1, false));
    EXPECT_FALSE(watch.Update(110 * kKB, 40 * kKB, t + RemoteIDGuard::kResumeHoldOffMs, false));

    // Each further pause doubles the hold-off.
    t += 10 * RemoteIDGuard::kResumeHoldOffMs;
    EXPECT_TRUE(watch.Update(80 * kKB, 8 * kKB, t, true));  // Largest block too small.
    EXPECT_EQ(watch.HoldOffMs(), 2 * RemoteIDGuard::kResumeHoldOffMs);
    EXPECT_TRUE(watch.Update(110 * kKB, 40 * kKB, t + 2 * RemoteIDGuard::kResumeHoldOffMs - 1, false));
    EXPECT_FALSE(watch.Update(110 * kKB, 40 * kKB, t + 2 * RemoteIDGuard::kResumeHoldOffMs, false));

    // The hold-off is capped.
    for (int i = 0; i < 20; i++) {
        t += RemoteIDGuard::kResumeHoldOffMaxMs;
        watch.Update(10 * kKB, 10 * kKB, t, true);
    }
    EXPECT_EQ(watch.HoldOffMs(), RemoteIDGuard::kResumeHoldOffMaxMs);
    EXPECT_FALSE(watch.Update(110 * kKB, 40 * kKB, t + RemoteIDGuard::kResumeHoldOffMaxMs, false));

    // Reset clears the back-off.
    watch.Reset();
    EXPECT_FALSE(watch.IsPaused());
    EXPECT_EQ(watch.HoldOffMs(), RemoteIDGuard::kResumeHoldOffMs);
}

TEST(RemoteIDGuard, HeapWatchHandlesClockWrap) {
    RemoteIDGuard::HeapWatch watch;
    const uint32_t t = UINT32_MAX - 1000;
    EXPECT_TRUE(watch.Update(10 * kKB, 10 * kKB, t, true));
    EXPECT_TRUE(watch.Update(110 * kKB, 40 * kKB, t + 2000, false));
    EXPECT_FALSE(watch.Update(110 * kKB, 40 * kKB, t + RemoteIDGuard::kResumeHoldOffMs, false));
}

TEST(RemoteIDGuard, BlockedReason) {
    EXPECT_EQ(RemoteIDGuard::BlockedReason(0), nullptr);
    EXPECT_EQ(RemoteIDGuard::BlockedReason(RemoteIDGuard::kStatusBLEActive), nullptr);
    // Ethernet without PSRAM: WiFi beacon paused, Bluetooth running.
    EXPECT_STREQ(RemoteIDGuard::BlockedReason(RemoteIDGuard::kStatusBlockedByNetwork |
                                              RemoteIDGuard::kStatusBLEActive),
                 "partly paused: this ESP32 has no PSRAM, so with Ethernet on only the Bluetooth transports run");
    EXPECT_NE(strstr(RemoteIDGuard::BlockedReason(RemoteIDGuard::kStatusBlockedByNetwork), "with WiFi on"), nullptr);
    EXPECT_NE(strstr(RemoteIDGuard::BlockedReason(RemoteIDGuard::kStatusPausedLowHeap), "web server"), nullptr);
    // A heap pause stops everything, so it explains more than a partial network block.
    EXPECT_NE(strstr(RemoteIDGuard::BlockedReason(RemoteIDGuard::kStatusPausedLowHeap |
                                                  RemoteIDGuard::kStatusBlockedByNetwork),
                     "web server"),
              nullptr);
    EXPECT_NE(strstr(RemoteIDGuard::BlockedReason(RemoteIDGuard::kStatusTxBlocked), "could not start"), nullptr);
    EXPECT_NE(strstr(RemoteIDGuard::BlockedReason(RemoteIDGuard::kStatusTxBlocked | RemoteIDGuard::kStatusBlockedByRAM),
                     "memory"),
              nullptr);
}

TEST(RemoteIDGuard, TransportsStr) {
    char buf[RemoteIDGuard::kTransportsStrMaxLen];
    EXPECT_STREQ(RemoteIDGuard::TransportsStr(0, buf, sizeof(buf)), "NONE");
    EXPECT_STREQ(RemoteIDGuard::TransportsStr(RemoteIDGuard::kTransportsBLE, buf, sizeof(buf)), "BT4+BT5_LR");
    EXPECT_STREQ(RemoteIDGuard::TransportsStr(RemoteIDGuard::kTransportsAll, buf, sizeof(buf)),
                 "BT4+BT5_LR+WIFI_BEACON");
    EXPECT_STREQ(RemoteIDGuard::TransportsStr(RemoteIDGuard::kTransportWiFiBeacon, buf, sizeof(buf)), "WIFI_BEACON");
    // Bits without a name print as hex.
    EXPECT_STREQ(RemoteIDGuard::TransportsStr(0x09, buf, sizeof(buf)), "BT4+0x8");
}

TEST(RemoteIDGuard, StatusStr) {
    char buf[RemoteIDGuard::kStatusStrMaxLen];
    EXPECT_STREQ(RemoteIDGuard::StatusStr(0, buf, sizeof(buf)), "NONE");
    EXPECT_STREQ(RemoteIDGuard::StatusStr(RemoteIDGuard::kStatusBLEActive | RemoteIDGuard::kStatusBLECodedPHYActive,
                                          buf, sizeof(buf)),
                 "BT_SCANNING+BT5_LR_SCANNING");
    EXPECT_STREQ(RemoteIDGuard::StatusStr(RemoteIDGuard::kStatusPausedLowHeap, buf, sizeof(buf)), "PAUSED_LOW_HEAP");
    EXPECT_STREQ(RemoteIDGuard::StatusStr(RemoteIDGuard::kStatusBlockedByNetwork | RemoteIDGuard::kStatusTxBlocked, buf,
                                          sizeof(buf)),
                 "BLOCKED_NETWORK+TX_BLOCKED");
    // Every bit set fits the buffer, and a short buffer truncates without overrunning.
    EXPECT_LT(strlen(RemoteIDGuard::StatusStr(0xFFFF, buf, sizeof(buf))), sizeof(buf) - 1);
    char tiny[8];
    EXPECT_STREQ(RemoteIDGuard::StatusStr(RemoteIDGuard::kStatusBlockedByRAM, tiny, sizeof(tiny)), "BLOCKED");
}

TEST(RemoteIDGuard, ParseTransports) {
    uint8_t t = 0xFF;
    EXPECT_TRUE(RemoteIDGuard::ParseTransports("BT4+BT5_LR", t));
    EXPECT_EQ(t, RemoteIDGuard::kTransportsBLE);
    EXPECT_TRUE(RemoteIDGuard::ParseTransports("WIFI_BEACON", t));
    EXPECT_EQ(t, RemoteIDGuard::kTransportWiFiBeacon);
    EXPECT_TRUE(RemoteIDGuard::ParseTransports("BT5_LR+BT4+WIFI_BEACON", t));
    EXPECT_EQ(t, RemoteIDGuard::kTransportsAll);
    EXPECT_TRUE(RemoteIDGuard::ParseTransports("ALL", t));
    EXPECT_EQ(t, RemoteIDGuard::kTransportsAll);
    EXPECT_TRUE(RemoteIDGuard::ParseTransports("NONE", t));
    EXPECT_EQ(t, 0);
    // The older numeric mask still works.
    EXPECT_TRUE(RemoteIDGuard::ParseTransports("3", t));
    EXPECT_EQ(t, 3);
    EXPECT_TRUE(RemoteIDGuard::ParseTransports("0x07", t));
    EXPECT_EQ(t, 7);
    EXPECT_TRUE(RemoteIDGuard::ParseTransports("0", t));
    EXPECT_EQ(t, 0);

    t = 5;
    for (const char* bad : {"", "8", "0x10", "BT6", "bt4", "BT4+", "+BT4", "BT4++BT5_LR", "BT4,BT5_LR", "3a", "0x"}) {
        EXPECT_FALSE(RemoteIDGuard::ParseTransports(bad, t)) << bad;
        EXPECT_EQ(t, 5) << bad;
    }
    // Every printed form parses back.
    char buf[RemoteIDGuard::kTransportsStrMaxLen];
    for (uint8_t v = 0; v <= RemoteIDGuard::kTransportsAll; v++) {
        EXPECT_TRUE(RemoteIDGuard::ParseTransports(RemoteIDGuard::TransportsStr(v, buf, sizeof(buf)), t));
        EXPECT_EQ(t, v);
    }
}
