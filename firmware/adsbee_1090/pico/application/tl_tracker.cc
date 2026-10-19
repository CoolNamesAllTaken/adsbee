#include "tl_tracker.hh"

#include <math.h>

namespace {
int Clamp(int value, int lo, int hi) { return value < lo ? lo : (value > hi ? hi : value); }
}  // namespace

int TLTracker::Start(int offset_mv, const Config &config) {
    config_ = config;
    if (config_.probe_s < 2) config_.probe_s = 2;
    config_.probe_s &= ~1u;
    if (config_.max_offset_mv < config_.min_offset_mv) config_.max_offset_mv = config_.min_offset_mv;
    offset_mv_ = Clamp(offset_mv, config_.min_offset_mv, config_.max_offset_mv);
    num_steps_ = 0;
    BeginProbe();
    return Applied();
}

void TLTracker::BeginProbe() {
    probing_ = true;
    seconds_ = 0;
    upper_first_ = true;
    num_pairs_ = 0;
    sum_diff_ = 0.0f;
    sum_diff_sq_ = 0.0f;
}

int TLTracker::Applied() const {
    if (!probing_) return offset_mv_;
    // Pair k covers seconds 2k and 2k+1; the first of each pair alternates side.
    bool first_of_pair = (seconds_ & 1) == 0;
    bool upper = first_of_pair == upper_first_;
    int dither = upper ? config_.dither_mv : -config_.dither_mv;
    return Clamp(offset_mv_ + dither, config_.min_offset_mv, config_.max_offset_mv);
}

int TLTracker::Update(uint32_t valid_frames) {
    seconds_++;
    if (!probing_) {
        if (seconds_ >= config_.hold_s) BeginProbe();
        return Applied();
    }

    if (seconds_ & 1) {
        first_frames_ = valid_frames;  // First second of a pair.
    } else {
        float diff = static_cast<float>(first_frames_) - static_cast<float>(valid_frames);
        if (!upper_first_) diff = -diff;
        sum_diff_ += diff;
        sum_diff_sq_ += diff * diff;
        num_pairs_++;
        upper_first_ = !upper_first_;
    }
    if (seconds_ < config_.probe_s) return Applied();

    // Probe done: step toward the better side if the pairs say so clearly.
    bool stepped = false;
    if (num_pairs_ >= 2) {
        float mean = sum_diff_ / num_pairs_;
        float variance = (sum_diff_sq_ - num_pairs_ * mean * mean) / (num_pairs_ - 1);
        if (variance > 0.0f) {
            float z = mean / sqrtf(variance / num_pairs_);
            int next = offset_mv_;
            if (z > config_.z_threshold) next += config_.step_mv;
            if (z < -config_.z_threshold) next -= config_.step_mv;
            next = Clamp(next, config_.min_offset_mv, config_.max_offset_mv);
            if (next != offset_mv_) {
                offset_mv_ = next;
                num_steps_++;
                stepped = true;
            }
        }
    }
    if (stepped || config_.hold_s == 0) {
        BeginProbe();
    } else {
        probing_ = false;
        seconds_ = 0;
    }
    return Applied();
}
