#pragma once

#include "glm/glm.hpp"
#include "glm/gtc/quaternion.hpp"

// Draws a 3D wireframe cube (with hidden-line occlusion) onto the current EPD
// Paint framebuffer, to visualize a device's fused orientation. The cube is fixed
// in the WORLD frame; as the device rotates, the cube is shown from a new angle —
// as if it were embedded behind the screen (a window onto a world-fixed cube).
//
// q_world_from_body is the device orientation (body->world), e.g. from
// SensorFusion::GetFusedQuaternion(). Orthographic projection.
//   cx, cy : box center in EPD draw-space pixels.
//   scale  : pixels per unit cube half-edge. Keep scale*sqrt(2) <= box half-size
//            so projected vertices stay in-bounds (Paint_DrawLine does not clip).
//
// Uses only GLM + Paint_DrawLine; draws into the global Paint context.
void DrawOrientationCube(int cx, int cy, float scale,
                         const glm::quat& q_world_from_body);
