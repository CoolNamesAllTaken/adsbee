// MLAT time base and pairing rule (mlat/mlat_pairing.hh).
#include "gtest/gtest.h"
#include "mlat/mlat_pairing.hh"

static constexpr uint64_t kUs = MlatTimebase::kTicksPerUs;
static constexpr uint64_t kPeriodTicks = 1u << MlatTimebase::kCounterBits;

// A sweep whose level request goes out at request_ticks; the answer comes 170 us later (one main-loop pass).
static MlatPairer::Sweep SweepAt(uint64_t request_ticks) {
    MlatPairer::Sweep sweep;
    sweep.level_request_ticks = request_ticks;
    sweep.level_answer_ticks = request_ticks + 170 * kUs;
    return sweep;
}

struct PairTest : testing::Test {
    MlatPairer pairer;
    uint64_t stamps[MlatPairer::kMaxReadPackets] = {};
    bool stamped[MlatPairer::kMaxReadPackets] = {};

    // A read of num_packets packets whose level request went out at request_ticks. Returns how many got stamps.
    uint16_t Read(uint64_t request_ticks, uint16_t num_packets) {
        MlatPairer::Sweep sweep = SweepAt(request_ticks);
        return pairer.Pair(sweep, num_packets, sweep.level_answer_ticks + 500 * kUs, stamps, stamped);
    }
};

TEST_F(PairTest, LonePacketIsStamped) {
    const uint64_t edge = 10000 * kUs;
    pairer.AddEdge(edge);
    ASSERT_EQ(Read(edge + 200 * kUs, 1), 1);
    EXPECT_TRUE(stamped[0]);
    EXPECT_EQ(stamps[0], edge);
    EXPECT_EQ(pairer.counters().stamped, 1u);
}

TEST_F(PairTest, EdgesMatchingPacketsAreStampedInOrder) {
    // Close pairs: 140 us apart, the shortest gap between two 112-bit packets.
    const uint64_t a = 10000 * kUs, b = a + 140 * kUs, c = b + 300 * kUs;
    pairer.AddEdge(a);
    pairer.AddEdge(b);
    pairer.AddEdge(c);
    ASSERT_EQ(Read(c + 200 * kUs, 3), 3);
    EXPECT_EQ(stamps[0], a);
    EXPECT_EQ(stamps[1], b);
    EXPECT_EQ(stamps[2], c);
    EXPECT_EQ(pairer.counters().stamped, 3u);
}

TEST_F(PairTest, FullFifoReadIsStamped) {
    uint64_t t = 10000 * kUs;
    uint64_t edges[18];
    for (uint64_t& e : edges) {
        e = t;
        pairer.AddEdge(e);
        t += 150 * kUs;
    }
    ASSERT_EQ(Read(t + 200 * kUs, 18), 18);
    for (uint16_t i = 0; i < 18; i++) {
        EXPECT_EQ(stamps[i], edges[i]) << i;
    }
}

TEST_F(PairTest, PacketWithoutEdgeLeavesTheReadUnstamped) {
    // The second sync event came while the latch was still set: two packets, one edge. Which packet the edge
    // belongs to is unknown, so neither is stamped.
    const uint64_t a = 10000 * kUs;
    pairer.AddEdge(a);
    EXPECT_EQ(Read(a + 600 * kUs, 2), 0);
    EXPECT_FALSE(stamped[0]);
    EXPECT_FALSE(stamped[1]);
    EXPECT_EQ(pairer.counters().unstamped_more_packets, 2u);
    EXPECT_EQ(pairer.counters().stamped, 0u);
}

TEST_F(PairTest, PacketWithoutAnyEdgeIsNotStamped) {
    EXPECT_EQ(Read(10000 * kUs, 1), 0);
    EXPECT_FALSE(stamped[0]);
    EXPECT_EQ(pairer.counters().unstamped_more_packets, 1u);
}

TEST_F(PairTest, EdgeWithoutPacketLeavesTheReadUnstamped) {
    // An edge surely in the read with no packet for it: the counts disagree, so no packet is trusted.
    const uint64_t a = 10000 * kUs, b = a + 200 * kUs;
    pairer.AddEdge(a);
    pairer.AddEdge(b);
    EXPECT_EQ(Read(b + 600 * kUs, 1), 0);
    EXPECT_EQ(pairer.counters().unstamped_more_edges, 1u);
    EXPECT_EQ(pairer.counters().orphan_events, 1u);
}

TEST_F(PairTest, EdgeWithoutPacketInAnEmptyReadIsCounted) {
    const uint64_t edge = 10000 * kUs;
    pairer.AddEdge(edge);
    EXPECT_EQ(Read(edge + 200 * kUs, 0), 0);
    EXPECT_EQ(pairer.counters().orphan_events, 1u);
    EXPECT_EQ(pairer.num_pending(), 0);
}

TEST_F(PairTest, YoungEdgeIsLeftForTheNextRead) {
    // b is too young to be in the first read, which holds a only.
    const uint64_t a = 10000 * kUs, b = a + 300 * kUs;
    pairer.AddEdge(a);
    pairer.AddEdge(b);
    ASSERT_EQ(Read(b + 50 * kUs, 1), 1);
    EXPECT_EQ(stamps[0], a);
    ASSERT_EQ(Read(b + 1000 * kUs, 1), 1);
    EXPECT_EQ(stamps[0], b);
}

TEST_F(PairTest, EventAtTheHardBoundIsInTheRead) {
    const uint64_t request = 10000 * kUs, edge = request - 145 * kUs;
    pairer.AddEdge(edge);
    ASSERT_EQ(Read(request, 1), 1);
    EXPECT_EQ(stamps[0], edge);
}

TEST_F(PairTest, AmbiguousEdgeCarriesOverAfterAMatchedRead) {
    // b sits between "surely in" and "surely later" for the first read. The counts agree (one packet, one sure
    // edge), so b's packet was not in it and b stays usable.
    const uint64_t a = 10000 * kUs, b = a + 300 * kUs;
    pairer.AddEdge(a);
    pairer.AddEdge(b);
    ASSERT_EQ(Read(b + 100 * kUs, 1), 1);  // b + 145 us > request, b + 125 us <= answer.
    ASSERT_EQ(Read(b + 2000 * kUs, 1), 1);
    EXPECT_EQ(stamps[0], b);
}

TEST_F(PairTest, AmbiguousEdgeIsDroppedAfterAMismatch) {
    const uint64_t a = 10000 * kUs, b = a + 300 * kUs;
    pairer.AddEdge(a);
    pairer.AddEdge(b);
    EXPECT_EQ(Read(b + 100 * kUs, 2), 0);   // b's packet may be the second one.
    EXPECT_EQ(Read(b + 2000 * kUs, 1), 0);  // b is unknown now: its packet may have been read.
    EXPECT_EQ(pairer.counters().unstamped_more_packets, 3u);
}

TEST_F(PairTest, AmbiguousEdgeOfAnEmptyReadWaitsForTheNextRead) {
    const uint64_t request = 10000 * kUs, edge = request - 100 * kUs;
    pairer.AddEdge(edge);
    EXPECT_EQ(Read(request, 0), 0);
    ASSERT_EQ(Read(request + 600 * kUs, 1), 1);
    EXPECT_EQ(stamps[0], edge);
}

TEST_F(PairTest, EdgeThatMayBeInAnEarlierReadIsDropped) {
    const uint64_t first_request = 10000 * kUs;
    EXPECT_EQ(Read(first_request, 1), 0);  // A read with no known event; it sets the boundary.
    // An edge old enough to have been in that read (reported late by the capture ring).
    const uint64_t edge = first_request + 170 * kUs - 130 * kUs;
    pairer.AddEdge(edge);
    EXPECT_EQ(Read(first_request + 600 * kUs, 1), 0);
    EXPECT_EQ(pairer.counters().stamped, 0u);
}

TEST_F(PairTest, NothingIsStampedAcrossAnUnpairedRead) {
    // FIFO overflow resync or an IRQ-paced chain read: edges before it may belong to packets it took.
    const uint64_t edge = 10000 * kUs;
    pairer.AddEdge(edge);
    pairer.Break(edge + 300 * kUs);
    pairer.CountUnpaired(9);
    EXPECT_EQ(Read(edge + 600 * kUs, 1), 0);
    EXPECT_EQ(pairer.counters().unstamped_unpaired, 9u);

    // An edge younger than the break that may still have been in the unpaired read.
    const uint64_t near_edge = edge + 300 * kUs - 130 * kUs;
    pairer.AddEdge(near_edge);
    EXPECT_EQ(Read(edge + 1200 * kUs, 1), 0);

    // Pairing resumes with the next edge.
    const uint64_t next = edge + 5000 * kUs;
    pairer.AddEdge(next);
    ASSERT_EQ(Read(next + 300 * kUs, 1), 1);
    EXPECT_EQ(stamps[0], next);
}

TEST_F(PairTest, StalledMainLoopLeavesOldEdgesUnstamped) {
    // The UAT radio or the console held the main loop: the sweep runs long after the event.
    const uint64_t edge = 10000 * kUs;
    pairer.AddEdge(edge);
    MlatPairer::Sweep sweep = SweepAt(edge + 150000 * kUs);
    EXPECT_EQ(pairer.Pair(sweep, 1, sweep.level_answer_ticks, stamps, stamped), 0);
    EXPECT_EQ(pairer.counters().stamped, 0u);
}

TEST_F(PairTest, YoungEdgeHoldsTheSweepBack) {
    const uint64_t edge = 10000 * kUs;
    EXPECT_FALSE(pairer.HasYoungEdge(edge));
    pairer.AddEdge(edge);
    EXPECT_TRUE(pairer.HasYoungEdge(edge + 20 * kUs));
    EXPECT_TRUE(pairer.HasYoungEdge(edge + 144 * kUs));
    // From here a sweep's level request finds the packet surely in the read.
    EXPECT_FALSE(pairer.HasYoungEdge(edge + 145 * kUs));
    ASSERT_EQ(Read(edge + 145 * kUs, 1), 1);
    EXPECT_EQ(stamps[0], edge);
}

TEST_F(PairTest, PendingQueueOverflowDropsEverything) {
    uint64_t t = 10000 * kUs;
    for (uint16_t i = 0; i <= MlatPairer::kMaxPendingEdges; i++) {
        pairer.AddEdge(t);
        t += 200 * kUs;
    }
    EXPECT_EQ(pairer.num_pending(), 1);
    EXPECT_EQ(pairer.counters().dropped_edges, MlatPairer::kMaxPendingEdges);
}

TEST_F(PairTest, MorePacketsThanAReadCanHoldAreNotStamped) {
    uint64_t t = 10000 * kUs;
    for (uint16_t i = 0; i < MlatPairer::kMaxReadPackets + 1; i++) {
        pairer.AddEdge(t);
        t += 150 * kUs;
    }
    EXPECT_EQ(Read(t + 200 * kUs, MlatPairer::kMaxReadPackets + 1), 0);
    EXPECT_EQ(pairer.counters().stamped, 0u);
}

TEST_F(PairTest, PairsAcrossCounterRollovers) {
    // Edges and sweeps from 24-bit captures, extended by the time base while the counter wraps several times.
    MlatTimebase timebase;
    uint64_t now = 3 * kPeriodTicks - 2000 * kUs;
    uint32_t now_us = 0xFFFFF000;  // The system clock wraps too.
    timebase.Start(static_cast<uint32_t>(now), now_us, now);
    uint64_t edge = now + 100 * kUs;
    for (int i = 0; i < 4000; i++) {  // 4000 reads, 1 ms apart: past 11 counter wraps.
        now += 1000 * kUs;
        now_us += 1000;
        ASSERT_TRUE(timebase.Update(static_cast<uint32_t>(now) & MlatTimebase::kCounterMask, now_us));
        pairer.AddEdge(timebase.Extend(static_cast<uint32_t>(edge) & MlatTimebase::kCounterMask));
        MlatPairer::Sweep sweep;
        sweep.level_request_ticks = timebase.Extend(static_cast<uint32_t>(now - 300 * kUs) & MlatTimebase::kCounterMask);
        sweep.level_answer_ticks = timebase.Extend(static_cast<uint32_t>(now - 130 * kUs) & MlatTimebase::kCounterMask);
        ASSERT_EQ(pairer.Pair(sweep, 1, timebase.ticks(), stamps, stamped), 1) << i;
        ASSERT_EQ(stamps[0], edge) << i;
        edge += 1000 * kUs;
    }
}

TEST(MlatTimebase, CountsAcrossRollovers) {
    MlatTimebase timebase;
    uint32_t now_us = 123456;
    uint64_t true_ticks = 5 * kPeriodTicks - 1000;  // Starts just before a wrap.
    timebase.Start(static_cast<uint32_t>(true_ticks), now_us, true_ticks);
    for (int i = 0; i < 5000; i++) {  // 170 us passes over 0.85 s: two wraps.
        now_us += 170;
        true_ticks += 170 * kUs;
        ASSERT_TRUE(timebase.Update(static_cast<uint32_t>(true_ticks) & MlatTimebase::kCounterMask, now_us));
        ASSERT_EQ(timebase.ticks(), true_ticks);
    }
}

TEST(MlatTimebase, LongGapsAreBridgedByTheSystemClock) {
    // Gaps of several counter periods, with the system clock 3 % fast or slow and 100 us coarse.
    for (double clock_error : {-0.03, 0.0, 0.03}) {
        MlatTimebase timebase;
        uint32_t now_us = 0xFFFF0000;  // The system clock wraps too.
        uint64_t true_ticks = 777;
        timebase.Start(static_cast<uint32_t>(true_ticks), now_us, true_ticks);
        for (uint32_t gap_us : {100u, 349000u, 349600u, 350000u, 524000u, 700000u, 1234567u, 1900000u, 170u}) {
            true_ticks += static_cast<uint64_t>(gap_us) * kUs;
            now_us += static_cast<uint32_t>(gap_us * (1.0 + clock_error)) / 100 * 100;
            ASSERT_TRUE(timebase.Update(static_cast<uint32_t>(true_ticks) & MlatTimebase::kCounterMask, now_us))
                << gap_us;
            ASSERT_EQ(timebase.ticks(), true_ticks) << gap_us << " " << clock_error;
            EXPECT_EQ(timebase.gap_ticks(), static_cast<uint64_t>(gap_us) * kUs);
        }
    }
}

TEST(MlatTimebase, GapBeyondTheLimitIsRefused) {
    MlatTimebase timebase;
    timebase.Start(0, 1000, 0);
    EXPECT_TRUE(timebase.Update(100, 1000 + MlatTimebase::kMaxGapUs));
    EXPECT_FALSE(timebase.Update(200, 1000 + 2 * MlatTimebase::kMaxGapUs + 1));
}

TEST(MlatTimebase, ExtendsCapturesBeforeTheLastUpdate) {
    MlatTimebase timebase;
    const uint64_t start = 3 * kPeriodTicks + 100;
    timebase.Start(100, 0, start);
    // A capture 2 ms before an update that crossed a wrap.
    const uint64_t capture = start + kPeriodTicks - 100 - 2000 * kUs;
    const uint64_t update = capture + 2000 * kUs + 500;
    ASSERT_TRUE(timebase.Update(static_cast<uint32_t>(update) & MlatTimebase::kCounterMask,
                                static_cast<uint32_t>((update - start) / kUs)));
    EXPECT_EQ(timebase.Extend(static_cast<uint32_t>(capture) & MlatTimebase::kCounterMask), capture);
}
