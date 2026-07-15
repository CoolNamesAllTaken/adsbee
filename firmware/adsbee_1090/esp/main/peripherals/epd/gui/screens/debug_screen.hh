#ifndef DEBUG_SCREEN_HH_
#define DEBUG_SCREEN_HH_

#include "canvas.hh"

// Forward declarations of the sensor drivers used by the debug screen, so this
// header stays lightweight. Their headers are included in debug_screen.cpp.
class Ltr329;
class Aht20;
class Spl06003;
class Mmc5603;
class Mp2722;
class Bq27427;
class Lsm6dsv;
class SensorFusion;

namespace winglet_ui {

// Bundle of live sensor references the debug screen renders. Populated by the
// ScreenManager from the application's driver instances.
struct DebugScreenSources {
    Ltr329& ltr;
    Aht20& aht;
    Spl06003& spl;
    Mmc5603& mmc;
    Mp2722& mp;
    Bq27427& bq;
    Lsm6dsv& imu;
    SensorFusion& fusion;
};

// Debug screen — the original sensor telemetry dump. The caller must have
// already cleared the canvas.
void DrawDebugScreen(Canvas& c, const DebugScreenSources& src);

}  // namespace winglet_ui

#endif  // DEBUG_SCREEN_HH_
