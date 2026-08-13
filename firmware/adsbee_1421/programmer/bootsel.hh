#pragma once

// Reads the BOOTSEL button. Briefly stalls flash access with interrupts off; keep calls to a
// modest cadence (tens of ms) so UART RX interrupts are not starved.
bool GetBootselButton();
