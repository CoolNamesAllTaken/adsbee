#include "settings_migration.hh"

#include <cstring>  // memcpy

// The frozen nested layouts must stay byte-identical to the live ones for the raw copies below to be valid. If a future
// version changes CoreNetworkSettings or RxPosition, these fire and the migration steps must switch to field-by-field
// copies for those members.
static_assert(sizeof(settings_v12::CoreNetworkSettings) == sizeof(SettingsManager::Settings::CoreNetworkSettings),
              "v12 CoreNetworkSettings layout diverged from live; migration copy is no longer valid.");
static_assert(sizeof(settings_v12::RxPosition) == sizeof(SettingsManager::RxPosition),
              "v12 RxPosition layout diverged from live; migration copy is no longer valid.");

void SettingsMigrator::MigrateV12ToV13(const settings_v12::Settings& in, SettingsManager::Settings& out) {
    // Start from a fresh, fully-defaulted current struct so any fields added since v12 (remote_id_rx_enabled,
    // remote_id_transports) take their current defaults and, on the RP2040, DeviceInfo-seeded defaults are applied.
    out = SettingsManager::Settings();

    out.settings_version = kSettingsVersion;

    // Network settings: byte-identical block, copied verbatim (CRC stays valid so it re-validates downstream).
    memcpy(&out.core_network_settings, &in.core_network_settings, sizeof(in.core_network_settings));

    // 1090 / system settings.
    out.r1090_rx_enabled = in.r1090_rx_enabled;
    out.tl_offset_mv = in.tl_offset_mv;
    out.r1090_bias_tee_enabled = in.r1090_bias_tee_enabled;
    out.watchdog_timeout_sec = in.watchdog_timeout_sec;

    // Communications settings (enum members re-widened from their stored underlying types).
    out.log_level = static_cast<SettingsManager::LogLevel>(in.log_level);
    for (uint16_t i = 0; i < SettingsManager::SerialInterface::kNumSerialInterfaces; i++) {
        out.reporting_protocols[i] = static_cast<SettingsManager::ReportingProtocol>(in.reporting_protocols[i]);
        out.baud_rates[i] = in.baud_rates[i];
    }

    // Sub-GHz settings.
    out.subg_enabled = static_cast<SettingsManager::EnableState>(in.subg_enabled);
    out.subg_rx_enabled = in.subg_rx_enabled;
    out.subg_bias_tee_enabled = in.subg_bias_tee_enabled;
    out.subg_mode = static_cast<SettingsManager::SubGHzRadioMode>(in.subg_mode);

    // remote_id_rx_enabled / remote_id_transports intentionally left at their v13 defaults (new in v13).

    // Feed settings (all fixed-size arrays; enum arrays re-widened element-by-element).
    memcpy(out.feed_uris, in.feed_uris, sizeof(in.feed_uris));
    memcpy(out.feed_ports, in.feed_ports, sizeof(in.feed_ports));
    memcpy(out.feed_is_active, in.feed_is_active, sizeof(in.feed_is_active));
    for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
        out.feed_protocols[i] = static_cast<SettingsManager::ReportingProtocol>(in.feed_protocols[i]);
    }
    memcpy(out.feed_receiver_ids, in.feed_receiver_ids, sizeof(in.feed_receiver_ids));

    // MAVLINK settings.
    out.mavlink_system_id = in.mavlink_system_id;
    out.mavlink_component_id = in.mavlink_component_id;

    // Receiver position (byte-identical packed layout).
    memcpy(&out.rx_position, &in.rx_position, sizeof(in.rx_position));
}

bool SettingsMigrator::Migrate(const uint8_t* blob, uint16_t blob_len, uint32_t from_version,
                               SettingsManager::Settings& out) {
    switch (from_version) {
        case 12: {
            if (blob_len < sizeof(settings_v12::Settings)) {
                return false;  // Stored blob too short to be a valid v12 struct.
            }
            // Copy into a properly-aligned local rather than reinterpret_cast'ing the (possibly-unaligned) blob.
            settings_v12::Settings v12;
            memcpy(&v12, blob, sizeof(v12));
            MigrateV12ToV13(v12, out);  // v13 is currently the latest; add further steps here as versions are added.
            return true;
        }
        // As new versions are added, add `case 13:` etc. that start the chain mid-way (e.g. MigrateV13ToV14(...)).
        default:
            // Older than kOldestMigratableVersion, unknown, or already current: nothing to migrate.
            return false;
    }
}
