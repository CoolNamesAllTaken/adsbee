#include <cmath>
#include <cstdint>
#include <random>

#include "../application/tl_learner.hh"
#include "gtest/gtest.h"

namespace {

// Valid frames per second for a trigger level offset: peaks at peak_mv, falls off on both sides.
float FramesAt(int offset_mv, int peak_mv = 450) {
    float x = (offset_mv - peak_mv) / 300.0f;
    return 150.0f * expf(-x * x);
}

/**
 * Runs learning to the end, one Update per second. Traffic scales every second's frames by
 * traffic(second); Poisson noise on top.
 */
template <typename Traffic>
int RunLearning(TLLearner &learner, int start_mv, const TLLearner::Config &config, uint32_t seed, Traffic traffic,
                int *seconds_out = nullptr) {
    std::mt19937 rng(seed);
    int offset = learner.Start(start_mv, config);
    int seconds = 0;
    while (learner.IsActive() && seconds < 100000) {
        float mean = FramesAt(offset) * traffic(seconds);
        uint32_t frames = std::poisson_distribution<uint32_t>(mean)(rng);
        offset = learner.Update(frames, rng(), rng());
        EXPECT_GE(offset, config.min_offset_mv);
        EXPECT_LE(offset, config.max_offset_mv);
        seconds++;
    }
    if (seconds_out) *seconds_out = seconds;
    EXPECT_FALSE(learner.IsActive());
    return offset;
}

float Steady(int) { return 1.0f; }

}  // namespace

TEST(TLLearner, StartsFromTheOffsetInUse) {
    TLLearner learner;
    EXPECT_EQ(learner.Start(600, {}), 600);
    EXPECT_TRUE(learner.IsActive());
    EXPECT_EQ(learner.GetAcceptedOffsetMV(), 600);
    EXPECT_EQ(learner.GetTemperatureMV(), 1000);
}

TEST(TLLearner, ConvergesNearThePeak) {
    for (uint32_t seed = 1; seed <= 20; seed++) {
        TLLearner learner;
        int result = RunLearning(learner, 600, {}, seed, Steady);
        EXPECT_NEAR(result, 450, 120) << "seed " << seed;
    }
}

TEST(TLLearner, ConvergesWhileTrafficChanges) {
    // Traffic halves and recovers over the run, with a 20 % swing every few minutes.
    auto traffic = [](int s) { return 0.75f + 0.25f * cosf(s / 600.0f) + 0.2f * sinf(s / 97.0f); };
    for (uint32_t seed = 1; seed <= 20; seed++) {
        TLLearner learner;
        int result = RunLearning(learner, 900, {}, seed, traffic);
        EXPECT_NEAR(result, 450, 150) << "seed " << seed;
    }
}

TEST(TLLearner, TakesTheConfiguredTime) {
    TLLearner learner;
    int seconds = 0;
    RunLearning(learner, 600, {.num_cycles = 10, .seconds_per_cycle = 6, .start_temperature_mv = 100}, 3, Steady,
                &seconds);
    EXPECT_EQ(seconds, 1 + 10 * 6);  // One settling second, then the cycles.
    EXPECT_EQ(learner.GetCycle(), 10);
    EXPECT_EQ(learner.GetTemperatureMV(), 0);
}

TEST(TLLearner, EndsAfterTheConfiguredCyclesWhateverTheTemperature) {
    // The default schedule doesn't divide evenly, and here there are more cycles than millivolts.
    TLLearner::Config many_cycles = {.num_cycles = 500, .seconds_per_cycle = 2, .start_temperature_mv = 100};
    for (TLLearner::Config config : {TLLearner::Config{}, many_cycles}) {
        TLLearner learner;
        int seconds = 0;
        RunLearning(learner, 600, config, 4, Steady, &seconds);
        EXPECT_EQ(seconds, 1 + config.num_cycles * config.seconds_per_cycle);
        EXPECT_EQ(learner.GetCycle(), config.num_cycles);
    }
}

TEST(TLLearner, AlternatesTheTwoOffsets) {
    TLLearner learner;
    std::mt19937 rng(5);
    learner.Start(500, {.seconds_per_cycle = 6});
    int candidate = learner.Update(100, rng(), rng());  // Settling second.
    EXPECT_EQ(candidate, learner.GetCandidateOffsetMV());
    int expected[] = {500, candidate, 500, candidate, 500};
    for (int e : expected) {
        EXPECT_EQ(learner.Update(100, rng(), rng()), e);
    }
}

TEST(TLLearner, StaysInsideBounds) {
    // Large steps near the lower bound must clamp to it, not wrap to the upper bound.
    TLLearner learner;
    TLLearner::Config config = {.num_cycles = 50, .seconds_per_cycle = 2, .start_temperature_mv = 1000,
                                .min_offset_mv = 200, .max_offset_mv = 900};
    RunLearning(learner, 250, config, 6, Steady);
}

TEST(TLLearner, ClampsTheStartingOffset) {
    TLLearner learner;
    EXPECT_EQ(learner.Start(50, {.min_offset_mv = 200, .max_offset_mv = 900}), 200);
}

TEST(TLLearner, StepsDownAsOftenAsUp) {
    // Equal frames: every candidate is accepted, so the accepted offset follows the proposal steps.
    TLLearner learner;
    std::mt19937 rng(7);
    learner.Start(1000, {.num_cycles = 200, .seconds_per_cycle = 2, .start_temperature_mv = 200});
    int ups = 0, downs = 0, previous = learner.GetAcceptedOffsetMV();
    while (learner.IsActive()) {
        learner.Update(100, rng(), rng());
        int accepted = learner.GetAcceptedOffsetMV();
        if (accepted > previous) ups++;
        if (accepted < previous) downs++;
        previous = accepted;
    }
    EXPECT_GT(downs, 60);
    EXPECT_GT(ups, 60);
}

TEST(TLLearner, RejectsAMuchWorseCandidateWhenCold) {
    TLLearner learner;
    learner.Start(500, {.num_cycles = 1, .seconds_per_cycle = 2, .start_temperature_mv = 10});
    learner.Update(0, 0, 0);                                 // Settling; candidate = 500 - 10.
    learner.Update(10, 0, 0);                                // Candidate second: few frames.
    EXPECT_EQ(learner.Update(70000, 0, 0xFFFFFFFF), 500);    // Accepted second: many (above int16).
    EXPECT_FALSE(learner.IsActive());
}

TEST(TLLearner, AcceptsABetterCandidate) {
    TLLearner learner;
    learner.Start(500, {.num_cycles = 1, .seconds_per_cycle = 2, .start_temperature_mv = 10});
    learner.Update(0, 3, 0);                                 // Settling; candidate = 500 - 10 + 3.
    EXPECT_EQ(learner.GetCandidateOffsetMV(), 493);
    learner.Update(70000, 0, 0xFFFFFFFF);                    // Candidate second.
    EXPECT_EQ(learner.Update(60000, 0, 0xFFFFFFFF), 493);    // Accepted second.
}

TEST(TLLearner, StopEndsLearning) {
    TLLearner learner;
    learner.Start(500, {});
    learner.Stop();
    EXPECT_FALSE(learner.IsActive());
    EXPECT_EQ(learner.GetTemperatureMV(), 0);
    EXPECT_EQ(learner.Update(1000, 1, 1), 500);
}
