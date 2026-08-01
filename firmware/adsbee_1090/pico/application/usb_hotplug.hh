#pragma once

// USB hot-plug re-enumeration workaround for self-powered RP2040 boards.
//
// The pico-sdk forces VBUS "always present" (usb_hw->pwr = VBUS_DETECT | VBUS_DETECT_OVERRIDE_EN),
// so on a self-powered board the USB D+ pull-up is asserted once at stdio_init_all() time and is
// never re-presented. A host that attaches AFTER the board is already powered therefore never sees
// a fresh connect edge and never enumerates the CDC serial device.
//
// UsbHotplugInit() starts a repeating timer that, while the device is not enumerated, periodically
// drops and re-asserts the D+ pull-up. Each re-assert manufactures a fresh attach edge, so a host
// that appears after boot enumerates within ~1 s. This works for a "cold" hot-plug (device never
// enumerated since boot), unlike a tud_resume_cb hook, which requires a prior enumerated session.
//
// The image stays universal: on a bus-powered device the port is present at boot, the device
// enumerates immediately and stays mounted, so the timer takes its "already mounted" early return
// forever and never toggles. No board-type gating and no USB descriptor changes are required.
//
// Call once, on core0, after stdio/USB has been initialized (i.e. after CommsManager::Init()).
void UsbHotplugInit();
