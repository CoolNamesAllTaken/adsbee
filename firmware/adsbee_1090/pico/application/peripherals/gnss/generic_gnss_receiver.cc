#include "generic_gnss_receiver.hh"

#include "comms.hh"

bool GenericGNSSReceiver::Init() {
    // Hold the receiver off while uart0 and its pins are configured. This prevents startup bytes
    // from arriving at an old baud rate or while the UART peripheral is being reset.
    SetEnable(false);
    ClaimUart();
    comms_manager.SetBaudRate(SettingsManager::kGNSSUART, GetDefaultBaudrate());
    EnableRxInterrupt();

    if (config_.pps_pin != UINT16_MAX) {
        gpio_init(config_.pps_pin);
        gpio_set_dir(config_.pps_pin, GPIO_IN);
        gpio_pull_down(config_.pps_pin);
        pps_last_level_ = gpio_get(config_.pps_pin);
    }

    // Generic receivers need no probe, boot delay, or manufacturer-specific configuration. Once
    // powered, the inherited Update() loop immediately listens for standard NMEA-0183 sentences.
    initializing_ = false;
    suspended_ = false;
    healthy_ = true;
    notify_observed_valid_ = false;
    notify_last_emitted_valid_ = false;
    notify_pending_ = false;
    notify_has_emitted_ = false;
    notify_last_timestamp_ms_ = 0;
    SetEnable(true);
    return true;
}
