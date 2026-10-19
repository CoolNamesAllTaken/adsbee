#pragma once

#include <cstdint>

/**
 * Learns the trigger level offset by simulated annealing on the number of valid Mode S frames received.
 *
 * Each cycle compares a candidate offset with the accepted one. The two take turns, one second each, so a change in
 * traffic during the cycle affects both alike. A candidate that received at least as many valid frames becomes the
 * accepted offset; a worse one is accepted with a probability that shrinks as the temperature drops. The next
 * candidate is a random step of up to the temperature from the accepted offset. When the temperature reaches zero,
 * the accepted offset is the result.
 *
 * Hardware free: the caller counts frames once per second, applies the returned offset and supplies random numbers.
 */
class TLLearner {
   public:
    // A candidate this much worse (as a fraction of the accepted offset's frames) is accepted with probability 1/e at
    // the start temperature.
    static constexpr float kAcceptScale = 0.05f;

    struct Config {
        uint16_t num_cycles = 60;
        uint16_t seconds_per_cycle = 20;  // Split evenly between the accepted and the candidate offset.
        uint16_t start_temperature_mv = 1000;
        int min_offset_mv = 0;
        int max_offset_mv = 2000;
    };

    /**
     * Begins learning from the offset currently in use.
     * @param[in] current_offset_mv Offset in use now.
     * @param[in] config Search schedule and bounds.
     * @retval Offset to use for the first second.
     */
    int Start(int current_offset_mv, const Config &config);

    /**
     * Ends learning early. The caller keeps whatever offset it applies.
     */
    void Stop() { active_ = false; }

    /**
     * Called once per second while learning.
     * @param[in] valid_frames Valid Mode S frames received during the second that just ended, which used the offset
     * returned by the previous call (or Start).
     * @param[in] random_step Random value for the next candidate's step.
     * @param[in] random_accept Random value for accepting a worse candidate.
     * @retval Offset to use for the next second (the learned offset once learning is done).
     */
    int Update(uint32_t valid_frames, uint32_t random_step, uint32_t random_accept);

    bool IsActive() const { return active_; }
    uint16_t GetTemperatureMV() const { return active_ ? temperature_mv_ : 0; }
    uint16_t GetCycle() const { return cycle_; }
    uint16_t GetNumCycles() const { return config_.num_cycles; }
    int GetAcceptedOffsetMV() const { return accepted_offset_mv_; }
    int GetCandidateOffsetMV() const { return candidate_offset_mv_; }

   private:
    void NextCandidate(uint32_t random_step);

    Config config_;
    bool active_ = false;
    bool settling_ = false;  // First second after Start.
    uint16_t cycle_ = 0;
    uint16_t temperature_mv_ = 0;
    int accepted_offset_mv_ = 0;
    int candidate_offset_mv_ = 0;
    uint16_t second_ = 0;              // Seconds measured in this cycle.
    bool candidate_applied_ = false;   // Offset in use during the current second.
    uint32_t accepted_frames_ = 0;     // This cycle, accepted offset.
    uint32_t candidate_frames_ = 0;    // This cycle, candidate offset.
};
