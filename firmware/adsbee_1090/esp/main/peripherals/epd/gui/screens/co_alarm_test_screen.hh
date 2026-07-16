#ifndef CO_ALARM_TEST_SCREEN_HH_
#define CO_ALARM_TEST_SCREEN_HH_

#include "canvas.hh"

class CoSensor;  // Forward declared; the full header is included in the .cpp.

namespace winglet_ui {

// CO Alarm Test screen. Shows the live CO reading and prompts the user to hold OK to sound the buzzer
// siren. `siren_active` reflects whether OK is currently held (the buzzer is driven by app_main).
// The caller must have already cleared the canvas.
void DrawCoAlarmTestScreen(Canvas& c, const CoSensor& co, bool siren_active);

}  // namespace winglet_ui

#endif  // CO_ALARM_TEST_SCREEN_HH_
