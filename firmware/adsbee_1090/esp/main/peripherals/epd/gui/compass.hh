#pragma once

#include "canvas.hh"

// Draws a North-up, phone-style debug compass onto the given Canvas
// to visualize the MAGNETOMETER-only heading (independent of the IMU fusion). A dial
// circle with N/E/S/W ticks and up to two bearing needles pointing toward magnetic
// North:
//   - solid needle  = tilt-compensated heading (IMU-leveled field)
//   - dotted needle = raw flat-plane heading   (mag X/Y only, no IMU)
// As the device tilts, the two needles diverge -- that divergence is the diagnostic.
//
//   cx, cy : dial center in EPD draw-space pixels.
//   radius : dial radius in pixels.
//   heading_level_deg / heading_flat_deg : phone-compass bearings (0..360, CW, N up),
//       e.g. from SensorFusion::GetMagHeadingLevelDeg() / GetMagHeadingFlatDeg().
//   valid  : false until the mag is calibrated; draws the dial + a "--" marker only.
//
// Draws into the given Canvas.
void DrawCompass(winglet_ui::Canvas& canvas, int cx, int cy, int radius,
                 float heading_level_deg, float heading_flat_deg, bool valid);
