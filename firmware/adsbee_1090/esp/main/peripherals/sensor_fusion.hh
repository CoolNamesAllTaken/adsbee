#pragma once

#include <cstdint>

#include "glm/glm.hpp"
#include "glm/gtc/quaternion.hpp"
#include "lsm6dsv.hh"
#include "mmc5603.hh"

// Sensor fusion: merge the IMU's gravity-referenced SFLP quaternion with the
// magnetometer into a single orientation quaternion referenced to gravity AND
// magnetic north (a standard AHRS attitude).
//
// Approach (yaw-correction, NOT a from-scratch AHRS): the LSM6DSV SFLP quaternion
// already gives good pitch/roll but its yaw drifts (no magnetometer). We compute
// an absolute magnetic heading from a tilt-compensated eCompass (using the SFLP
// quaternion's roll/pitch for tilt compensation) and steer the SFLP yaw toward it
// with a complementary filter. Hard-iron offsets are auto-calibrated live from the
// running per-axis min/max of the field while the device is rotated.
//
// The fused quaternion is the raw SFLP body->world attitude quaternion (fed directly
// to the standard aerospace ZYX extractors; see SflpToAircraftAttitude in the .cpp),
// with only a fixed device->aircraft mounting trim applied. Euler outputs follow the
// GDL90 AHRS conventions: heading magnetic 0-360, pitch + = nose/top up, roll + =
// right side down. The mounting trim is a single fixed rotation in Config, not a
// per-attitude fit.
//
// This object OWNS references to the IMU and magnetometer drivers and is the single
// integration point: Update() drives mag.Update() and reads both sensors. (The IMU
// quaternion is refreshed asynchronously by the IMU's INT2 reader task, so the IMU
// is only read, never Update()'d here.)
//
// FRAME / SIGN ASSUMPTIONS are all funnelled through Config so they can be flipped
// on the bench without touching the algorithm. Defaults are best-effort; each is
// flagged VERIFY-ON-HARDWARE in the .cpp.

class SensorFusion {
 public:
  struct Config {
    // ---- Mag sensor-frame -> IMU body-frame orientation ----
    // Proper rotation taking a raw magnetometer sample into the IMU body frame.
    // Board geometry (both chips +Z out the device back; IMU +Y = device down,
    // mag +X = device up) is a -90 deg rotation about the shared +Z axis:
    //   IMU_X<-+magY, IMU_Y<--magX, IMU_Z<-+magZ.  (VERIFY ON HARDWARE)
    glm::quat mag_to_imu = glm::angleAxis(glm::radians(-90.f), glm::vec3(0.f, 0.f, 1.f));

    // ---- Mag hard-iron seed offsets (gauss, body frame) ----
    float seed_offset_g[3] = {0.f, 0.f, 0.f};

    // ---- Frame / sign conventions (VERIFY ON HARDWARE) ----
    // NOTE: the AHRS attitude output does NOT use this flag. The SFLP game rotation vector is fed
    // RAW to the extractors (see SflpToAircraftAttitude) — conjugating it inverts the rotation and
    // cross-couples roll with yaw. This flag is only consumed by the (currently disabled)
    // mag/eCompass path below, where it controls the eCompass tilt-compensation frame.
    bool  imu_quat_conjugate = true;

    // ---- Device-body -> aircraft-body mounting rotation (VERIFY ON HARDWARE) ----
    // Right-multiplied onto the raw SFLP attitude quaternion (see SflpToAircraftAttitude). This is
    // a pure yaw-independent trim for the physical mounting: it aligns the device axes to the
    // aircraft convention but does NOT affect the roll<->yaw decoupling.
    //
    // Composed from two bench-fit steps:
    //   1. 180 deg about the (1,1,0) diagonal — undoes the raw frame's roll<->pitch swap + inversion
    //      (with identity: right-wing-down read as nose-down and level read upside down).
    //   2. -90 deg about the aircraft right/pitch axis (Y) — re-zeros pitch so the device held with
    //      its nose pointing straight up reads as level (pitch 0).
    // Net = angleAxis(180,(1,1,0)) * angleAxis(-90,(0,1,0)) = quat(0.5, 0.5, 0.5, -0.5).
    // NOTE: with the nose-up reference, device lean fwd/back -> AHRS pitch, but device roll about
    // its long axis -> AHRS yaw and device yaw -> AHRS roll (roll/yaw swap at this orientation, by
    // design choice).
    glm::quat body_mount =
        glm::angleAxis(glm::radians(180.f), glm::normalize(glm::vec3(1.f, 1.f, 0.f))) *
        glm::angleAxis(glm::radians(-90.f), glm::vec3(0.f, 1.f, 0.f));

    // Heading is CW-from-north (opposite chirality to the right-handed yaw the
    // extractor produces), so it carries its own sign. -1 makes CW rotation increase
    // the reported heading. This is the dedicated GDL90 heading mechanism, kept
    // separate from the attitude transform (body_mount).
    float heading_sign       = -1.f;   // +1 = CW-from-North; -1 to invert
    float declination_deg    = 0.f;    // add for true north
    // Constant heading offset (deg) for the GDL90 heading. Bench-trim against a known
    // heading so North reads ~0. If CW rotation makes heading DECREASE, flip
    // heading_sign above.
    float heading_offset_deg = 0.f;

    // ---- Complementary filter (mag steers the drifting SFLP yaw) ----
    // Master switch for the mag yaw correction. When false, the fused output is pure
    // IMU attitude (yaw_offset_ stays 0) and the mag is read but not fused. Disabled
    // for now while the magnetometer readings are still suspect.
    bool  mag_correction_enabled = false;
    float tau_sec  = 2.0f;    // mag time constant; if >0 used instead of mag_gain
    float mag_gain = 0.02f;   // fixed per-update blend when tau_sec <= 0

    // ---- Hard-iron auto-calibration heuristic ----
    float min_span_gauss = 0.3f;   // per-axis min-max span required to trust heading
    float min_mag_gauss  = 0.05f;  // reject near-zero field

    // ---- dt fallback for the first call / non-positive measured dt ----
    float default_dt_sec = 1.0f / 30.0f;
  };

  struct FusedOrientation {
    // Body->world aircraft attitude quaternion: the raw SFLP game rotation vector with the fixed
    // mounting trim applied (see SflpToAircraftAttitude in the .cpp).
    glm::quat quaternion{1.f, 0.f, 0.f, 0.f};
    float yaw_deg     = 0.f;                    // aerospace ZYX yaw about world Z
    float heading_deg = 0.f;                    // GDL90 magnetic, 0..360, CW-from-north
    float pitch_deg   = 0.f;                    // + = nose/top up
    float roll_deg    = 0.f;                    // + = right side down
  };

  SensorFusion(Lsm6dsv& imu, Mmc5603& mag)
      : SensorFusion(imu, mag, Config{}) {}
  SensorFusion(Lsm6dsv& imu, Mmc5603& mag, const Config& config);

  SensorFusion(const SensorFusion&)            = delete;
  SensorFusion& operator=(const SensorFusion&) = delete;

  // Drives mag.Update(), reads both sensors, self-times dt, and fuses. Call from
  // the main loop in place of a standalone mag.Update().
  void Update();

  // ---- Getters (always safe; return the last fused result) ----
  const FusedOrientation& GetFusedOrientation() const { return fused_; }
  const glm::quat& GetFusedQuaternion() const { return fused_.quaternion; }
  float GetYawDeg()     const { return fused_.yaw_deg; }
  float GetHeadingDeg() const { return fused_.heading_deg; }
  float GetPitchDeg()   const { return fused_.pitch_deg; }
  float GetRollDeg()    const { return fused_.roll_deg; }

  bool IsValid()        const { return valid_; }          // IMU quaternion usable
  bool IsCalibrated()   const { return calibrated_; }     // mag span sufficient
  bool IsHeadingValid() const { return heading_valid_; }  // yaw correction active

  // ---- Mag-only debug headings (phone-compass bearing, 0..360, CW, North up) ----
  // Computed every Update() regardless of mag_correction_enabled, for the debug compass.
  // Level = tilt-compensated (IMU-leveled field); Flat = raw mag X/Y only (no IMU).
  float GetMagHeadingLevelDeg() const { return mag_heading_level_deg_; }
  float GetMagHeadingFlatDeg()  const { return mag_heading_flat_deg_; }
  bool  IsMagHeadingValid()     const { return mag_heading_valid_; }

  glm::vec3 GetHardIronOffsets() const {
    return glm::vec3(offset_[0], offset_[1], offset_[2]);
  }
  // Reset the running min/max (and offsets to the seed); keeps yaw_offset_ so the
  // heading doesn't snap.
  void ResetCalibration();

 private:
  // Rotate a raw field sample from the mag sensor frame into the IMU body frame.
  glm::vec3 RemapMag(const glm::vec3& raw) const;

  // Convert the raw SFLP game rotation vector (already a body->world attitude quaternion) to the
  // aircraft attitude quaternion, applying only config_.body_mount. See the .cpp for details.
  glm::quat SflpToAircraftAttitude(const glm::quat& q_sflp) const;

  Lsm6dsv& imu_;
  Mmc5603& mag_;
  const Config config_;

  FusedOrientation fused_;

  // Hard-iron auto-calibration state.
  float mag_min_[3];
  float mag_max_[3];
  float offset_[3];

  // Complementary-filter state (world-Z yaw correction, radians).
  float yaw_offset_ = 0.f;

  // Mag-only debug headings (deg, phone-compass bearing); see getters above.
  float mag_heading_level_deg_ = 0.f;
  float mag_heading_flat_deg_  = 0.f;
  bool  mag_heading_valid_     = false;

  // Self-timed dt.
  int64_t last_update_us_ = 0;  // 0 = first call

  bool valid_         = false;
  bool calibrated_    = false;
  bool heading_valid_ = false;
  bool logged_calibrated_ = false;  // one-shot ESP_LOGI latch
};
