#pragma once

#include <cstdint>

/**
 * Keeps the trigger level offset near the one that receives the most valid Mode S frames, in the background.
 *
 * Probes alternate the offset dither_mv above and below the tracked offset, one second each, and compare each pair of
 * seconds, so a change in traffic affects both sides alike. If the pairs show one side is better with a z score above
 * z_threshold, the tracked offset steps step_mv that way and the next probe starts at once. Otherwise the offset holds
 * still for hold_s seconds before the next probe.
 *
 * Hardware free: the caller counts frames once per second and applies the returned offset.
 */
class TLTracker {
   public:
    struct Config {
        int dither_mv = 50;
        int step_mv = 25;
        uint16_t probe_s = 120;  // Even: whole pairs.
        uint16_t hold_s = 480;
        float z_threshold = 2.0f;
        int min_offset_mv = 300;
        int max_offset_mv = 1200;
    };

    /**
     * Starts tracking from an offset (clamped to the bounds) with a probe.
     * @retval Offset to use for the next second.
     */
    int Start(int offset_mv, const Config &config);

    /**
     * Continues after a pause: a probe in progress starts over (its pairs are stale), a hold carries on.
     * @retval Offset to use for the next second.
     */
    int Resume() {
        if (probing_) BeginProbe();
        return Applied();
    }

    /**
     * Called once per second while tracking.
     * @param[in] valid_frames Valid Mode S frames received during the second that just ended, which used the offset
     * returned by the previous call (or Start).
     * @retval Offset to use for the next second.
     */
    int Update(uint32_t valid_frames);

    int GetOffsetMV() const { return offset_mv_; }
    bool IsProbing() const { return probing_; }
    uint32_t GetNumSteps() const { return num_steps_; }

   private:
    int Applied() const;
    void BeginProbe();

    Config config_;
    int offset_mv_ = 0;
    bool probing_ = false;
    uint16_t seconds_ = 0;     // Seconds into the current probe or hold.
    bool upper_first_ = true;  // Order within the current pair (alternates pair to pair).
    uint32_t first_frames_ = 0;
    // Pair differences (upper minus lower) this probe.
    uint16_t num_pairs_ = 0;
    float sum_diff_ = 0.0f;
    float sum_diff_sq_ = 0.0f;
    uint32_t num_steps_ = 0;
};
