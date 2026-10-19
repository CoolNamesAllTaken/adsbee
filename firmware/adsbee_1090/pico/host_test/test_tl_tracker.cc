#include <cmath>
#include <cstdint>
#include <random>
#include <vector>

#include "../application/tl_tracker.hh"
#include "gtest/gtest.h"

namespace {

struct CurvePoint {
    int mv;
    float gain;  // Valid frames relative to the peak.
};

// Valid frames against the offset, measured on a live antenna (offsets interleaved every 4 s for an hour).
const std::vector<CurvePoint> kLiveSky = {{300, 0.69}, {400, 0.83}, {450, 0.89}, {500, 0.95}, {550, 0.96}, {600, 0.98},
                                          {650, 1.00}, {700, 0.985}, {750, 0.975}, {800, 0.95}, {900, 0.87}, {1000, 0.77},
                                          {1200, 0.6}};
// A quieter site that peaks lower (bench sensitivity gains with little channel occupancy).
const std::vector<CurvePoint> kQuiet = {{300, 0.9}, {400, 0.97}, {500, 1.0}, {600, 0.985}, {700, 0.95}, {800, 0.9},
                                        {1000, 0.78}, {1200, 0.65}};

float Gain(const std::vector<CurvePoint> &curve, int mv) {
    if (mv <= curve.front().mv) return curve.front().gain;
    for (size_t i = 1; i < curve.size(); i++) {
        if (mv <= curve[i].mv) {
            float t = static_cast<float>(mv - curve[i - 1].mv) / (curve[i].mv - curve[i - 1].mv);
            return curve[i - 1].gain + t * (curve[i].gain - curve[i - 1].gain);
        }
    }
    return curve.back().gain;
}

struct Result {
    int final_mv;
    float mean_gain;  // Frames received relative to always sitting at the peak.
    int min_mv, max_mv;  // Tracked offset range after the first hour.
};

/**
 * Simulates `seconds` of tracking. Each second's frames are Poisson around peak_fps x gain x traffic(t), where traffic
 * swings slowly and has 15 % second-to-second burstiness.
 */
Result Simulate(const std::vector<CurvePoint> &curve, int start_mv, int seconds, float peak_fps, uint32_t seed,
                TLTracker::Config config = {}) {
    std::mt19937 rng(seed);
    std::lognormal_distribution<float> burst(0.0f, 0.15f);
    TLTracker tracker;
    int offset = tracker.Start(start_mv, config);
    double sum_gain = 0;
    Result r = {0, 0, 10000, 0};
    for (int s = 0; s < seconds; s++) {
        float traffic = 0.75f + 0.25f * cosf(s / 2000.0f) + 0.1f * sinf(s / 130.0f);
        float g = Gain(curve, offset);
        sum_gain += g;
        uint32_t frames = std::poisson_distribution<uint32_t>(peak_fps * g * traffic * burst(rng))(rng);
        offset = tracker.Update(frames);
        if (s > 3600) {
            r.min_mv = std::min(r.min_mv, tracker.GetOffsetMV());
            r.max_mv = std::max(r.max_mv, tracker.GetOffsetMV());
        }
    }
    r.final_mv = tracker.GetOffsetMV();
    r.mean_gain = sum_gain / seconds;
    return r;
}

}  // namespace

TEST(TLTracker, ProbesAroundTheOffsetInPairs) {
    TLTracker tracker;
    EXPECT_EQ(tracker.Start(600, {.probe_s = 8}), 650);
    // Pairs alternate their order: + -, - +, + -, ...
    int expected[] = {550, 550, 650, 650, 550};
    for (int e : expected) EXPECT_EQ(tracker.Update(100), e);
}

TEST(TLTracker, StepsTowardTheBetterSide) {
    TLTracker tracker;
    int offset = tracker.Start(600, {.probe_s = 40});
    for (int s = 0; s < 40; s++) offset = tracker.Update(offset > 600 ? 110 + s % 3 : 100 + s % 5);
    EXPECT_EQ(tracker.GetOffsetMV(), 625);
    EXPECT_TRUE(tracker.IsProbing());  // Keeps climbing.
}

TEST(TLTracker, HoldsWhenTheSidesAreEqual) {
    TLTracker tracker;
    std::mt19937 rng(1);
    int offset = tracker.Start(600, {.probe_s = 40, .hold_s = 100});
    for (int s = 0; s < 40; s++) offset = tracker.Update(std::poisson_distribution<uint32_t>(100)(rng));
    EXPECT_EQ(tracker.GetOffsetMV(), 600);
    EXPECT_FALSE(tracker.IsProbing());
    EXPECT_EQ(offset, 600);
    for (int s = 0; s < 99; s++) EXPECT_EQ(tracker.Update(100), 600);
    EXPECT_EQ(tracker.Update(100), 650);  // Next probe.
}

TEST(TLTracker, NoTrafficNoSteps) {
    TLTracker tracker;
    tracker.Start(600, {.probe_s = 20});
    for (int s = 0; s < 10000; s++) tracker.Update(0);
    EXPECT_EQ(tracker.GetOffsetMV(), 600);
    EXPECT_EQ(tracker.GetNumSteps(), 0u);
}

TEST(TLTracker, StaysInsideBounds) {
    TLTracker tracker;
    int offset = tracker.Start(320, {.probe_s = 10, .min_offset_mv = 300, .max_offset_mv = 400});
    for (int s = 0; s < 2000; s++) {
        offset = tracker.Update((offset < 330 ? 200 : 100) + s % 7);  // Always prefers lower.
        ASSERT_GE(offset, 300);
        ASSERT_LE(offset, 400);
    }
    EXPECT_EQ(tracker.GetOffsetMV(), 300);
}

TEST(TLTracker, FindsTheLiveSkyPeak) {
    for (int start : {400, 600, 1000}) {
        for (uint32_t seed = 1; seed <= 5; seed++) {
            Result r = Simulate(kLiveSky, start, 4 * 3600, 140.0f, seed);
            EXPECT_NEAR(r.final_mv, 650, 100) << "start " << start << " seed " << seed;
            EXPECT_GE(r.min_mv, 525) << "start " << start << " seed " << seed;
            EXPECT_LE(r.max_mv, 800) << "start " << start << " seed " << seed;
        }
    }
}

TEST(TLTracker, FindsAQuietSitePeak) {
    for (uint32_t seed = 1; seed <= 5; seed++) {
        Result r = Simulate(kQuiet, 600, 4 * 3600, 40.0f, seed);
        EXPECT_NEAR(r.final_mv, 500, 100) << "seed " << seed;
    }
}
