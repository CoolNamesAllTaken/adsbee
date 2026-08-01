#include "usb_hotplug.hh"

#include <cstdint>

#include "pico/time.h"  // For repeating_timer_t / add_repeating_timer_ms.

// TinyUSB device functions. We forward-declare them with C linkage rather than including "tusb.h":
// pico_stdio_usb keeps its TinyUSB device-stack config private to its own compilation, so including
// tusb.h here leaves the tud_* API undeclared (CFG_TUD_ENABLED is not visible to us). These symbols
// are compiled into pico_stdio_usb / TinyUSB and resolve at link time. Signatures verified against
// TinyUSB device/usbd.h. (tud_ready() is a header-only inline, so we use tud_mounted() directly.)
extern "C" {
bool tud_mounted(void);     // Device is enumerated and configured.
bool tud_disconnect(void);  // Disable the D+ pull-up.
bool tud_connect(void);     // Enable the D+ pull-up (re-present the device to the host).
}

namespace {

// Spacing between the disconnect and connect halves of a re-present, and the base timer period.
// ~250 ms is the value confirmed on the RPi forums to satisfy Windows 11 (macOS is more lenient).
constexpr int32_t kUsbReconnectTimerMs = 250;

// Two-phase state so no single timer callback has to block for the full spacing: one fire drops the
// pull-up, the next fire re-asserts it. The ~500 ms round trip repeats while unmounted, so a
// hot-plug enumerates within ~1 s.
enum class UsbReconnectPhase : uint8_t { kIdle, kDisconnected };
UsbReconnectPhase usb_phase = UsbReconnectPhase::kIdle;
repeating_timer_t usb_reconnect_timer;

// Fires every kUsbReconnectTimerMs on the default alarm pool (core0). Never cancelled: it keeps
// running forever and simply checks tud_mounted() each fire, which is how it self-heals across
// unplug/replug (there is no VBUS event to re-arm on) and stays inert on bus-powered devices.
bool UsbReconnectTimerCb(repeating_timer_t*) {
    if (tud_mounted()) {
        // Enumerated (or bus-powered and normally connected): nothing to do, stay idle.
        usb_phase = UsbReconnectPhase::kIdle;
        return true;
    }
    switch (usb_phase) {
        case UsbReconnectPhase::kIdle:
            // Drop the pull-up this fire...
            tud_disconnect();
            usb_phase = UsbReconnectPhase::kDisconnected;
            break;
        case UsbReconnectPhase::kDisconnected:
            // ...re-assert it next fire, manufacturing a fresh attach edge for a late host.
            tud_connect();
            usb_phase = UsbReconnectPhase::kIdle;
            break;
    }
    return true;  // Keep the timer running.
}

}  // namespace

void UsbHotplugInit() {
    add_repeating_timer_ms(kUsbReconnectTimerMs, UsbReconnectTimerCb, nullptr, &usb_reconnect_timer);
}
