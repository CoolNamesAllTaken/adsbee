#include "tl_learner.hh"

#include <math.h>

int TLLearner::Start(int current_offset_mv, const Config &config) {
    config_ = config;
    if (config_.num_cycles == 0) config_.num_cycles = 1;
    if (config_.seconds_per_cycle < 2) config_.seconds_per_cycle = 2;
    if (config_.max_offset_mv < config_.min_offset_mv) config_.max_offset_mv = config_.min_offset_mv;
    temperature_mv_ = config_.start_temperature_mv;
    int offset_mv = current_offset_mv;
    if (offset_mv < config_.min_offset_mv) offset_mv = config_.min_offset_mv;
    if (offset_mv > config_.max_offset_mv) offset_mv = config_.max_offset_mv;
    accepted_offset_mv_ = offset_mv;
    candidate_offset_mv_ = offset_mv;
    cycle_ = 0;
    second_ = 0;
    accepted_frames_ = 0;
    candidate_frames_ = 0;
    candidate_applied_ = false;
    settling_ = true;
    active_ = temperature_mv_ > 0;
    return accepted_offset_mv_;
}

void TLLearner::NextCandidate(uint32_t random_step) {
    // Uniform step in [-temperature, +temperature] from the accepted offset.
    int span = 2 * static_cast<int>(temperature_mv_) + 1;
    int step = static_cast<int>(random_step % static_cast<uint32_t>(span)) - static_cast<int>(temperature_mv_);
    int candidate = accepted_offset_mv_ + step;
    if (candidate < config_.min_offset_mv) candidate = config_.min_offset_mv;
    if (candidate > config_.max_offset_mv) candidate = config_.max_offset_mv;
    candidate_offset_mv_ = candidate;
}

int TLLearner::Update(uint32_t valid_frames, uint32_t random_step, uint32_t random_accept) {
    if (!active_) return accepted_offset_mv_;

    if (settling_) {
        // The first second only lets the starting offset settle (it isn't counted).
        settling_ = false;
        NextCandidate(random_step);
        candidate_applied_ = true;
        return candidate_offset_mv_;
    }

    (candidate_applied_ ? candidate_frames_ : accepted_frames_) += valid_frames;
    second_++;

    if (second_ < config_.seconds_per_cycle) {
        candidate_applied_ = !candidate_applied_;
        return candidate_applied_ ? candidate_offset_mv_ : accepted_offset_mv_;
    }

    // Cycle done: score the candidate against the accepted offset measured alongside it.
    float baseline = accepted_frames_ > 0 ? static_cast<float>(accepted_frames_) : 1.0f;
    float change = (static_cast<float>(candidate_frames_) - static_cast<float>(accepted_frames_)) / baseline;
    bool accept = change >= 0.0f;
    if (!accept) {
        float scale = kAcceptScale * temperature_mv_ / config_.start_temperature_mv;
        float probability = scale > 0.0f ? expf(change / scale) : 0.0f;
        accept = (random_accept >> 8) * (1.0f / (1u << 24)) < probability;
    }
    if (accept) accepted_offset_mv_ = candidate_offset_mv_;

    cycle_++;
    second_ = 0;
    accepted_frames_ = 0;
    candidate_frames_ = 0;
    if (cycle_ >= config_.num_cycles) {
        temperature_mv_ = 0;
        active_ = false;
        candidate_offset_mv_ = accepted_offset_mv_;
        return accepted_offset_mv_;
    }
    // Falls linearly to 1 mV in the last cycle.
    uint32_t temperature = static_cast<uint32_t>(config_.start_temperature_mv) * (config_.num_cycles - cycle_) /
                           config_.num_cycles;
    temperature_mv_ = temperature > 0 ? static_cast<uint16_t>(temperature) : 1;
    NextCandidate(random_step);
    // Alternate which offset goes first, so a steady traffic trend favors neither.
    candidate_applied_ = (cycle_ & 1) == 0;
    return candidate_applied_ ? candidate_offset_mv_ : accepted_offset_mv_;
}
