#include "orientation_cube.hh"

#include <cmath>
#include <cstdint>

#include "canvas.hh"  // Canvas draw methods, colors, line styles.

using winglet_ui::Canvas;

namespace {

// Cube vertices (world coords), ±1, indexed by (bit0=X, bit1=Y, bit2=Z).
constexpr glm::vec3 kVerts[8] = {
    {-1, -1, -1}, {+1, -1, -1}, {-1, +1, -1}, {+1, +1, -1},
    {-1, -1, +1}, {+1, -1, +1}, {-1, +1, +1}, {+1, +1, +1},
};

// Outward face normals: 0:-X 1:+X 2:-Y 3:+Y 4:-Z 5:+Z.
constexpr glm::vec3 kFaceNormals[6] = {
    {-1, 0, 0}, {+1, 0, 0}, {0, -1, 0}, {0, +1, 0}, {0, 0, -1}, {0, 0, +1},
};

// 12 edges: vertex pair {a,b} + the two faces {fa,fb} that share the edge. An
// edge is drawn iff at least one of its faces is front-facing (hidden-line
// occlusion: an edge is hidden only when BOTH faces are back-facing).
struct Edge {
  uint8_t a, b, fa, fb;
};
constexpr Edge kEdges[12] = {
    // along X: shared by a Y-face and a Z-face
    {0, 1, 2, 4}, {2, 3, 3, 4}, {4, 5, 2, 5}, {6, 7, 3, 5},
    // along Y: shared by an X-face and a Z-face
    {0, 2, 0, 4}, {1, 3, 1, 4}, {4, 6, 0, 5}, {5, 7, 1, 5},
    // along Z: shared by an X-face and a Y-face
    {0, 4, 0, 2}, {1, 5, 1, 2}, {2, 6, 0, 3}, {3, 7, 1, 3},
};

// Screen mapping signs (device +X=right, +Y=up; screen +Y is DOWN → flip Y).
// kSignX is -1 to flip the in-screen roll direction (horizontal mirror, accepted on
// hardware so roll tracks the device). Flip these if the cube mirrors/tilts wrong.
constexpr float kSignX  = -1.0f;
constexpr float kSignY  = -1.0f;
constexpr float kVisEps = 1e-4f;

// Round + clamp to the in-bounds range Canvas::DrawLine accepts (it rejects any
// endpoint > width/height; negatives would wrap, so clamp them to 0 too).
int ClampX(const Canvas& c, float v) {
  int i = static_cast<int>(lroundf(v));
  if (i < 0) i = 0;
  if (i > c.width()) i = c.width();
  return i;
}
int ClampY(const Canvas& c, float v) {
  int i = static_cast<int>(lroundf(v));
  if (i < 0) i = 0;
  if (i > c.height()) i = c.height();
  return i;
}

}  // namespace

void DrawOrientationCube(Canvas& canvas, int cx, int cy, float scale,
                         const glm::quat& q_world_from_body) {
  // Rotate world-fixed points into the device/screen frame. The fused quaternion is
  // already oriented for the device frame (imu_quat_conjugate is applied upstream), so
  // it is used directly -- the extra conjugate here reversed the rotation sense on all
  // three axes (cube spun opposite to the device).
  const glm::quat q = q_world_from_body;

  // Project all 8 vertices (orthographic).
  int sx[8], sy[8];
  for (int i = 0; i < 8; ++i) {
    const glm::vec3 p = q * kVerts[i];
    sx[i] = ClampX(canvas, static_cast<float>(cx) + kSignX * scale * p.x);
    sy[i] = ClampY(canvas, static_cast<float>(cy) + kSignY * scale * p.y);
  }

  // Front-facing test per face: device-frame normal points toward the viewer (+Z).
  bool vis[6];
  for (int f = 0; f < 6; ++f) {
    vis[f] = (q * kFaceNormals[f]).z > kVisEps;
  }

  // Draw edges with at least one visible face; skip occluded and degenerate edges.
  for (const Edge& e : kEdges) {
    if (!(vis[e.fa] || vis[e.fb])) continue;
    if (sx[e.a] == sx[e.b] && sy[e.a] == sy[e.b]) continue;
    canvas.DrawLine(sx[e.a], sy[e.a], sx[e.b], sy[e.b], winglet_ui::kBlack,
                    winglet_ui::kLineSolid, 1);
  }
}
