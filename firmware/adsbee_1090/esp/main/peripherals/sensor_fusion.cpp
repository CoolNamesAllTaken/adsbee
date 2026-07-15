#include "sensor_fusion.hh"

#include <algorithm>
#include <cmath>

#include "esp_log.h"
#include "esp_timer.h"

static const char* kTag = "SensorFusion";

namespace {

constexpr float kPi    = 3.14159265358979323846f;
constexpr float kTwoPi = 2.0f * kPi;
constexpr float kRad2Deg = 57.2957795130823f;

// Wrap an angle (radians) to [-pi, pi].
float WrapPi(float a) {
  a = fmodf(a + kPi, kTwoPi);
  if (a < 0.0f) a += kTwoPi;
  return a - kPi;
}

// Wrap degrees to [0, 360).
float Wrap360(float d) {
  d = fmodf(d, 360.0f);
  if (d < 0.0f) d += 360.0f;
  return d;
}

// Roll (rotation about body X) from a body->world quaternion {w,x,y,z}.
float QuatRoll(const glm::quat& q) {
  return atan2f(2.0f * (q.w * q.x + q.y * q.z),
                1.0f - 2.0f * (q.x * q.x + q.y * q.y));
}

// Pitch (rotation about body Y), with gimbal-lock clamp.
float QuatPitch(const glm::quat& q) {
  float s = 2.0f * (q.w * q.y - q.z * q.x);
  s = std::clamp(s, -1.0f, 1.0f);
  return asinf(s);
}

// Yaw (rotation about world Z) from a body->world quaternion.
float QuatYaw(const glm::quat& q) {
  return atan2f(2.0f * (q.w * q.z + q.x * q.y),
                1.0f - 2.0f * (q.y * q.y + q.z * q.z));
}

}  // namespace

SensorFusion::SensorFusion(Lsm6dsv& imu, Mmc5603& mag, const Config& config)
    : imu_(imu), mag_(mag), config_(config) {
  ResetCalibration();
}

void SensorFusion::ResetCalibration() {
  // Seed min/max to extremes so real samples immediately set them; offsets start
  // at the configured seed. yaw_offset_ is intentionally left untouched.
  for (int k = 0; k < 3; ++k) {
    mag_min_[k] = 1e9f;
    mag_max_[k] = -1e9f;
    offset_[k]  = config_.seed_offset_g[k];
  }
  calibrated_ = false;
}

glm::vec3 SensorFusion::RemapMag(const glm::vec3& raw) const {
  return config_.mag_to_imu * raw;
}

// Convert the LSM6DSV SFLP "game rotation vector" to the aircraft attitude quaternion consumed by
// the standard aerospace ZYX extractors (QuatRoll/QuatPitch/QuatYaw above).
//
// The SFLP quaternion is ALREADY a body->world attitude quaternion suitable for those extractors:
// it must be fed in RAW, with NO conjugation and NO frame relabel. This is confirmed by a proven
// LSM6DSV SFLP reference (kriswiner LSM6DSV_SFLP_Ladybug), which feeds sflpq={w,x,y,z} straight
// into the identical extractor formulas and gets correct, yaw-independent roll/pitch. Conjugating
// the quaternion inverts the rotation, and extracting ZYX Euler from an inverted rotation
// cross-couples roll with yaw (the inverse of a ZYX rotation is XYZ) — that was the coupling bug.
//
// The only transform applied is the fixed device-body -> aircraft-body mounting trim, right-
// multiplied on the body side. It is yaw-independent and cannot re-introduce coupling.
glm::quat SensorFusion::SflpToAircraftAttitude(const glm::quat& q_sflp) const {
  return glm::normalize(q_sflp * config_.body_mount);
}

void SensorFusion::Update() {
  // 1. Drive the magnetometer state machine (alternating mag/temp single-shots).
  mag_.Update();

  // Read the sensors. The IMU quaternion is refreshed asynchronously by the IMU's
  // INT2 reader task; we only read it here.
  glm::quat q_imu        = imu_.GetQuaternion();
  const glm::quat q_sflp_raw = q_imu;  // Raw SFLP game rotation vector, before any conjugation.
  const bool imu_valid   = imu_.IsQuaternionValid();
  const glm::vec3 mag_raw = mag_.GetMagneticFieldGauss();

  // Self-timed dt.
  const int64_t now_us = esp_timer_get_time();
  float dt = config_.default_dt_sec;
  if (last_update_us_ != 0) {
    const float measured = (now_us - last_update_us_) * 1e-6f;
    if (measured > 0.0f) dt = measured;
  }
  last_update_us_ = now_us;

  // 2. IMU gate: without a valid SFLP quaternion there is nothing to fuse.
  if (!imu_valid) {
    valid_         = false;
    heading_valid_ = false;
    fused_.quaternion = q_imu;  // harmless pass-through (identity until first INT2)
    return;
  }
  if (config_.imu_quat_conjugate) q_imu = glm::conjugate(q_imu);
  q_imu = glm::normalize(q_imu);

  // 3. Mag axis/sign remap into the IMU body frame.
  glm::vec3 m = RemapMag(mag_raw);

  // 4. Hard-iron auto-calibration: update running min/max on the remapped field.
  for (int k = 0; k < 3; ++k) {
    const float v = m[k];
    if (v < mag_min_[k]) mag_min_[k] = v;
    if (v > mag_max_[k]) mag_max_[k] = v;
    offset_[k] = 0.5f * (mag_min_[k] + mag_max_[k]);
  }
  const bool spans_ok =
      (mag_max_[0] - mag_min_[0]) > config_.min_span_gauss &&
      (mag_max_[1] - mag_min_[1]) > config_.min_span_gauss &&
      (mag_max_[2] - mag_min_[2]) > config_.min_span_gauss;
  calibrated_ = spans_ok;
  if (calibrated_ && !logged_calibrated_) {
    logged_calibrated_ = true;
    ESP_LOGI(kTag, "Mag calibration sufficient (spans x=%.2f y=%.2f z=%.2f G)",
             mag_max_[0] - mag_min_[0], mag_max_[1] - mag_min_[1],
             mag_max_[2] - mag_min_[2]);
  }

  // 5. Subtract hard-iron offset.
  m -= glm::vec3(offset_[0], offset_[1], offset_[2]);

  const float mag_norm = std::sqrt(m.x * m.x + m.y * m.y + m.z * m.z);
  const bool mag_usable = calibrated_ && (mag_norm > config_.min_mag_gauss);

  // 6. Tilt-compensated eCompass heading via full rotation: bring the body-frame field
  //    into the world frame with the gravity-referenced body->world quaternion, then
  //    take the horizontal heading. q_imu was conjugated above for the ATTITUDE output
  //    (imu_quat_conjugate); the eCompass needs the original gravity-referenced
  //    body->world orientation, so undo that conjugate here. (Confirmed from hardware:
  //    leveling with the attitude-output quaternion swings heading 80 deg under tilt;
  //    this form holds it to a few degrees.) yaw_imu uses the SAME quaternion so the
  //    IMU yaw cancels in `target`, preserving the drift-correction architecture.
  const glm::quat q_b2w = config_.imu_quat_conjugate ? glm::conjugate(q_imu) : q_imu;
  const glm::vec3 mw = q_b2w * m;

  // Signed eCompass heading (radians) used to steer the fused yaw.
  float mag_heading = config_.heading_sign * atan2f(mw.y, mw.x) +
                      config_.declination_deg * (kPi / 180.0f);
  mag_heading = WrapPi(mag_heading);

  // Mag-only debug headings (always computed, independent of mag_correction_enabled):
  // a phone-compass bearing (0..360, CW, North up). The tilt-compensated bearing uses
  // the leveled field (mw); the flat bearing uses the raw body-frame field (no IMU).
  mag_heading_valid_ = mag_usable;
  if (mag_usable) {
    mag_heading_level_deg_ = Wrap360(mag_heading * kRad2Deg);
    float flat = config_.heading_sign * atan2f(m.y, m.x) +
                 config_.declination_deg * (kPi / 180.0f);
    mag_heading_flat_deg_ = Wrap360(WrapPi(flat) * kRad2Deg);
  }

  if (config_.mag_correction_enabled && mag_usable) {
    // 7. Yaw error vs. the SFLP quaternion's current yaw, then complementary
    //    filter the world-Z yaw correction toward it.
    const float yaw_imu = QuatYaw(q_b2w);
    const float target  = WrapPi(mag_heading - yaw_imu);
    const float err     = WrapPi(target - yaw_offset_);

    float alpha = (config_.tau_sec > 0.0f) ? (dt / (config_.tau_sec + dt))
                                           : config_.mag_gain;
    alpha = std::clamp(alpha, 0.0f, 1.0f);
    yaw_offset_ = WrapPi(yaw_offset_ + alpha * err);
    heading_valid_ = true;
  } else {
    // Hold yaw_offset_; output carries the (uncorrected) SFLP yaw.
    heading_valid_ = false;
  }

  // 8. Fused attitude quaternion. The raw SFLP game rotation vector is already a body->world
  // attitude quaternion; feed it straight to the extractors (see SflpToAircraftAttitude), applying
  // only the fixed device->aircraft mounting trim. This is consumed by the GDL90 AHRS message and
  // the orientation cube.
  //
  // PATH A: the magnetometer yaw correction is currently disabled (mag_correction_enabled=false),
  // so yaw_offset_ is 0 and the drift-corrected quaternion is not applied here. When the mag path
  // is re-enabled it must steer yaw about the vertical; that reconciliation is a later pass.
  fused_.quaternion = SflpToAircraftAttitude(q_sflp_raw);

  // 9. Euler outputs from the NED attitude quaternion, using the standard aerospace ZYX extractors
  // (roll about body X, pitch about body Y, yaw about world Z). heading_deg applies the GDL90
  // magnetic-style convention (CW-from-north) via heading_sign + heading_offset_deg.
  const float yaw    = QuatYaw(fused_.quaternion) * kRad2Deg;
  fused_.yaw_deg     = yaw;
  fused_.roll_deg    = QuatRoll(fused_.quaternion) * kRad2Deg;
  fused_.pitch_deg   = QuatPitch(fused_.quaternion) * kRad2Deg;
  fused_.heading_deg = Wrap360(config_.heading_sign * yaw + config_.heading_offset_deg);
  valid_ = true;
}
