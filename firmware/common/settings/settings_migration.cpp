#include "settings_migration.hh"

#include <cstring>  // memcpy

// The migration chain must end at the live version. When kSettingsVersion is bumped, freeze v21 and extend the chain
// (see settings_migration.hh).
static_assert(kSettingsVersion == 21, "kSettingsVersion changed: freeze the previous layout and add a migration step.");
static_assert(sizeof(settings_v12::Settings) == 1088 && sizeof(settings_v13::Settings) == 1088 &&
                  sizeof(settings_v14::Settings) == 1140 && sizeof(settings_v15::Settings) == 1144 &&
                  sizeof(settings_v16::Settings) == 1144 && sizeof(settings_v17::Settings) == 1340 &&
                  sizeof(settings_v18::Settings) == 1340 && sizeof(settings_v19::Settings) == 2652 &&
                  sizeof(settings_v20::Settings) == 2716,
              "A frozen settings snapshot changed size. Frozen snapshots must never be edited.");

// The frozen nested layouts must stay byte-identical to the live ones for the raw copies below to be valid. If a future
// version changes CoreNetworkSettings or RxPosition, these fire and the migration steps must switch to field-by-field
// copies for those members.
static_assert(sizeof(settings_v18::CoreNetworkSettings) == sizeof(SettingsManager::Settings::CoreNetworkSettings),
              "v18 CoreNetworkSettings layout diverged from live; migration copy is no longer valid.");
static_assert(sizeof(settings_v18::RxPosition) == sizeof(SettingsManager::RxPosition),
              "v18 RxPosition layout diverged from live; migration copy is no longer valid.");
static_assert(sizeof(settings_v18::WiFiNetwork) == sizeof(SettingsManager::Settings::WiFiNetwork),
              "v18 WiFiNetwork layout diverged from live; migration copy is no longer valid.");
static_assert(sizeof(settings_v17::CoreNetworkSettings) == sizeof(settings_v18::CoreNetworkSettings),
              "v17 -> v18 CoreNetworkSettings layout changed; migration copy is no longer valid.");
static_assert(sizeof(settings_v17::RxPosition) == sizeof(settings_v18::RxPosition),
              "v17 -> v18 RxPosition layout changed; migration copy is no longer valid.");
static_assert(sizeof(settings_v17::WiFiNetwork) == sizeof(settings_v18::WiFiNetwork),
              "v17 -> v18 WiFiNetwork layout changed; migration copy is no longer valid.");
static_assert(sizeof(settings_v16::CoreNetworkSettings) == sizeof(settings_v17::CoreNetworkSettings),
              "v16 -> v17 CoreNetworkSettings layout changed; migration copy is no longer valid.");
static_assert(sizeof(settings_v16::RxPosition) == sizeof(settings_v17::RxPosition),
              "v16 -> v17 RxPosition layout changed; migration copy is no longer valid.");
static_assert(sizeof(settings_v15::CoreNetworkSettings) == sizeof(settings_v16::CoreNetworkSettings),
              "v15 -> v16 CoreNetworkSettings layout changed; migration copy is no longer valid.");
static_assert(sizeof(settings_v15::RxPosition) == sizeof(settings_v16::RxPosition),
              "v15 -> v16 RxPosition layout changed; migration copy is no longer valid.");
static_assert(sizeof(settings_v14::CoreNetworkSettings) == sizeof(settings_v15::CoreNetworkSettings),
              "v14 -> v15 CoreNetworkSettings layout changed; migration copy is no longer valid.");
static_assert(sizeof(settings_v14::RxPosition) == sizeof(settings_v15::RxPosition),
              "v14 -> v15 RxPosition layout changed; migration copy is no longer valid.");
static_assert(sizeof(settings_v13::CoreNetworkSettings) == sizeof(settings_v14::CoreNetworkSettings),
              "v13 -> v14 CoreNetworkSettings layout changed; migration copy is no longer valid.");
static_assert(sizeof(settings_v13::RxPosition) == sizeof(settings_v14::RxPosition),
              "v13 -> v14 RxPosition layout changed; migration copy is no longer valid.");
static_assert(sizeof(settings_v12::CoreNetworkSettings) == sizeof(settings_v13::CoreNetworkSettings),
              "v12 -> v13 CoreNetworkSettings layout changed; migration copy is no longer valid.");
static_assert(sizeof(settings_v12::RxPosition) == sizeof(settings_v13::RxPosition),
              "v12 -> v13 RxPosition layout changed; migration copy is no longer valid.");

void SettingsMigrator::MigrateV12ToV13(const settings_v12::Settings& in, settings_v13::Settings& out) {
    out = settings_v13::Settings{};
    out.settings_version = 13;

    // Network settings: byte-identical block.
    memcpy(&out.core_network_settings, &in.core_network_settings, sizeof(in.core_network_settings));

    out.r1090_rx_enabled = in.r1090_rx_enabled;
    out.tl_offset_mv = in.tl_offset_mv;
    out.r1090_bias_tee_enabled = in.r1090_bias_tee_enabled;
    out.watchdog_timeout_sec = in.watchdog_timeout_sec;

    out.log_level = in.log_level;
    for (uint16_t i = 0; i < settings_v13::kNumSerialInterfaces; i++) {
        out.reporting_protocols[i] = in.reporting_protocols[i];
        out.baud_rates[i] = in.baud_rates[i];
    }

    out.subg_enabled = in.subg_enabled;
    out.subg_rx_enabled = in.subg_rx_enabled;
    out.subg_bias_tee_enabled = in.subg_bias_tee_enabled;
    out.subg_mode = in.subg_mode;

    // Remote ID receive settings are new in v13. Match the live defaults (off; all transports selected) so a v12 unit
    // upgrading straight to v14 ends up with the same values it would have gotten from a fresh v13 struct.
    out.remote_id_rx_enabled = false;
    out.remote_id_transports = SettingsManager::kRemoteIDTransportBLE4 | SettingsManager::kRemoteIDTransportBLE5Long |
                               SettingsManager::kRemoteIDTransportWiFiBeacon;

    memcpy(out.feed_uris, in.feed_uris, sizeof(in.feed_uris));
    memcpy(out.feed_ports, in.feed_ports, sizeof(in.feed_ports));
    memcpy(out.feed_is_active, in.feed_is_active, sizeof(in.feed_is_active));
    memcpy(out.feed_protocols, in.feed_protocols, sizeof(in.feed_protocols));
    memcpy(out.feed_receiver_ids, in.feed_receiver_ids, sizeof(in.feed_receiver_ids));

    out.mavlink_system_id = in.mavlink_system_id;
    out.mavlink_component_id = in.mavlink_component_id;

    memcpy(&out.rx_position, &in.rx_position, sizeof(in.rx_position));
}

void SettingsMigrator::MigrateV13ToV14(const settings_v13::Settings& in, settings_v14::Settings& out) {
    out = settings_v14::Settings{};
    out.settings_version = 14;

    memcpy(&out.core_network_settings, &in.core_network_settings, sizeof(in.core_network_settings));

    out.r1090_rx_enabled = in.r1090_rx_enabled;
    out.tl_offset_mv = in.tl_offset_mv;
    out.r1090_bias_tee_enabled = in.r1090_bias_tee_enabled;
    out.watchdog_timeout_sec = in.watchdog_timeout_sec;
    out.led_enabled = true;  // New in v14; match the live default.
    // gnss_enabled/gnss_receiver_type/gnss_notify are new in v14; zero-init above matches their defaults (off, none).

    out.log_level = in.log_level;
    for (uint16_t i = 0; i < settings_v14::kNumSerialInterfaces; i++) {
        out.reporting_protocols[i] = in.reporting_protocols[i];
        out.baud_rates[i] = in.baud_rates[i];
    }

    out.subg_enabled = in.subg_enabled;
    out.subg_rx_enabled = in.subg_rx_enabled;
    out.subg_bias_tee_enabled = in.subg_bias_tee_enabled;
    out.subg_mode = in.subg_mode;

    // Remote ID receive settings carry over from v13.
    out.remote_id_rx_enabled = in.remote_id_rx_enabled;
    out.remote_id_transports = in.remote_id_transports;

    // Remote ID transmit settings are new in v14; left at their defaults (disabled, all transports, empty identity)
    // via the `settings_v14::Settings{}` zero-init above -- match the live defaults explicitly since this frozen
    // struct has no constructor to apply them.
    out.remote_id_tx_transports = SettingsManager::kRemoteIDTransportBLE4 |
                                  SettingsManager::kRemoteIDTransportBLE5Long |
                                  SettingsManager::kRemoteIDTransportWiFiBeacon;
    out.remote_id_tx_uas_id_type = 1;
    out.remote_id_tx_ua_type = 2;

    memcpy(out.feed_uris, in.feed_uris, sizeof(in.feed_uris));
    memcpy(out.feed_ports, in.feed_ports, sizeof(in.feed_ports));
    memcpy(out.feed_is_active, in.feed_is_active, sizeof(in.feed_is_active));
    memcpy(out.feed_protocols, in.feed_protocols, sizeof(in.feed_protocols));
    memcpy(out.feed_receiver_ids, in.feed_receiver_ids, sizeof(in.feed_receiver_ids));

    out.mavlink_system_id = in.mavlink_system_id;
    out.mavlink_component_id = in.mavlink_component_id;

    memcpy(&out.rx_position, &in.rx_position, sizeof(in.rx_position));
}

void SettingsMigrator::MigrateV14ToV15(const settings_v14::Settings& in, settings_v15::Settings& out) {
    out = settings_v15::Settings{};
    out.settings_version = 15;
    out.feeds_enabled = true;  // New in v15: enabled, so active feeds keep running.

    memcpy(&out.core_network_settings, &in.core_network_settings, sizeof(in.core_network_settings));

    out.r1090_rx_enabled = in.r1090_rx_enabled;
    out.tl_offset_mv = in.tl_offset_mv;
    out.r1090_bias_tee_enabled = in.r1090_bias_tee_enabled;
    out.watchdog_timeout_sec = in.watchdog_timeout_sec;
    out.led_enabled = in.led_enabled;
    out.gnss_enabled = in.gnss_enabled;
    out.gnss_receiver_type = in.gnss_receiver_type;
    out.gnss_notify = in.gnss_notify;

    out.log_level = in.log_level;
    for (uint16_t i = 0; i < SettingsManager::SerialInterface::kNumSerialInterfaces; i++) {
        out.reporting_protocols[i] = in.reporting_protocols[i];
        out.baud_rates[i] = in.baud_rates[i];
    }

    out.subg_enabled = in.subg_enabled;
    out.subg_rx_enabled = in.subg_rx_enabled;
    out.subg_bias_tee_enabled = in.subg_bias_tee_enabled;
    out.subg_mode = in.subg_mode;

    out.remote_id_rx_enabled = in.remote_id_rx_enabled;
    out.remote_id_transports = in.remote_id_transports;

    out.remote_id_tx_enabled = in.remote_id_tx_enabled;
    out.remote_id_tx_transports = in.remote_id_tx_transports;
    out.remote_id_tx_uas_id_type = in.remote_id_tx_uas_id_type;
    out.remote_id_tx_ua_type = in.remote_id_tx_ua_type;
    memcpy(out.remote_id_tx_uas_id, in.remote_id_tx_uas_id, sizeof(in.remote_id_tx_uas_id));
    memcpy(out.remote_id_tx_operator_id, in.remote_id_tx_operator_id, sizeof(in.remote_id_tx_operator_id));

    memcpy(out.feed_uris, in.feed_uris, sizeof(in.feed_uris));
    memcpy(out.feed_ports, in.feed_ports, sizeof(in.feed_ports));
    memcpy(out.feed_is_active, in.feed_is_active, sizeof(in.feed_is_active));
    for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
        out.feed_protocols[i] = in.feed_protocols[i];
    }
    memcpy(out.feed_receiver_ids, in.feed_receiver_ids, sizeof(in.feed_receiver_ids));

    out.mavlink_system_id = in.mavlink_system_id;
    out.mavlink_component_id = in.mavlink_component_id;

    memcpy(&out.rx_position, &in.rx_position, sizeof(in.rx_position));
}

void SettingsMigrator::MigrateV15ToV16(const settings_v15::Settings& in, settings_v16::Settings& out) {
    out = settings_v16::Settings{};
    out.settings_version = 16;

    memcpy(&out.core_network_settings, &in.core_network_settings, sizeof(in.core_network_settings));

    out.r1090_rx_enabled = in.r1090_rx_enabled;
    out.tl_offset_mv = in.tl_offset_mv;
    out.r1090_bias_tee_enabled = in.r1090_bias_tee_enabled;
    out.watchdog_timeout_sec = in.watchdog_timeout_sec;
    out.led_enabled = in.led_enabled;
    out.feeds_enabled = in.feeds_enabled;
    out.gnss_enabled = in.gnss_enabled;
    out.gnss_receiver_type = in.gnss_receiver_type;
    out.gnss_notify = in.gnss_notify;

    out.log_level = in.log_level;
    for (uint16_t i = 0; i < settings_v16::kNumSerialInterfaces; i++) {
        out.reporting_protocols[i] = in.reporting_protocols[i];
        out.baud_rates[i] = in.baud_rates[i];
    }

    out.subg_enabled = in.subg_enabled;
    out.subg_rx_enabled = in.subg_rx_enabled;
    out.subg_bias_tee_enabled = in.subg_bias_tee_enabled;
    out.subg_mode = in.subg_mode;

    out.remote_id_rx_enabled = in.remote_id_rx_enabled;
    out.remote_id_transports = in.remote_id_transports;

    out.remote_id_tx_enabled = in.remote_id_tx_enabled;
    out.remote_id_tx_transports = in.remote_id_tx_transports;
    out.remote_id_tx_uas_id_type = in.remote_id_tx_uas_id_type;
    out.remote_id_tx_ua_type = in.remote_id_tx_ua_type;
    memcpy(out.remote_id_tx_uas_id, in.remote_id_tx_uas_id, sizeof(in.remote_id_tx_uas_id));
    memcpy(out.remote_id_tx_operator_id, in.remote_id_tx_operator_id, sizeof(in.remote_id_tx_operator_id));

    memcpy(out.feed_uris, in.feed_uris, sizeof(in.feed_uris));
    memcpy(out.feed_ports, in.feed_ports, sizeof(in.feed_ports));
    memcpy(out.feed_is_active, in.feed_is_active, sizeof(in.feed_is_active));
    for (uint16_t i = 0; i < settings_v16::kMaxNumFeeds; i++) {
        out.feed_protocols[i] = in.feed_protocols[i];
    }
    memcpy(out.feed_receiver_ids, in.feed_receiver_ids, sizeof(in.feed_receiver_ids));

    out.mavlink_system_id = in.mavlink_system_id;
    out.mavlink_component_id = in.mavlink_component_id;

    memcpy(&out.rx_position, &in.rx_position, sizeof(in.rx_position));
    out.ip_mode = 1;  // New in v16: IPv4 + IPv6 (kIPModeDual).
}

void SettingsMigrator::MigrateV16ToV17(const settings_v16::Settings& in, settings_v17::Settings& out) {
    out = settings_v17::Settings{};  // Extra WiFi station networks (new in v17) start empty.
    out.settings_version = 17;

    memcpy(&out.core_network_settings, &in.core_network_settings, sizeof(in.core_network_settings));

    out.r1090_rx_enabled = in.r1090_rx_enabled;
    out.tl_offset_mv = in.tl_offset_mv;
    out.r1090_bias_tee_enabled = in.r1090_bias_tee_enabled;
    out.watchdog_timeout_sec = in.watchdog_timeout_sec;
    out.led_enabled = in.led_enabled;
    out.feeds_enabled = in.feeds_enabled;
    out.gnss_enabled = in.gnss_enabled;
    out.gnss_receiver_type = in.gnss_receiver_type;
    out.gnss_notify = in.gnss_notify;

    out.log_level = in.log_level;
    for (uint16_t i = 0; i < settings_v17::kNumSerialInterfaces; i++) {
        out.reporting_protocols[i] = in.reporting_protocols[i];
        out.baud_rates[i] = in.baud_rates[i];
    }

    out.subg_enabled = in.subg_enabled;
    out.subg_rx_enabled = in.subg_rx_enabled;
    out.subg_bias_tee_enabled = in.subg_bias_tee_enabled;
    out.subg_mode = in.subg_mode;

    out.remote_id_rx_enabled = in.remote_id_rx_enabled;
    out.remote_id_transports = in.remote_id_transports;

    out.remote_id_tx_enabled = in.remote_id_tx_enabled;
    out.remote_id_tx_transports = in.remote_id_tx_transports;
    out.remote_id_tx_uas_id_type = in.remote_id_tx_uas_id_type;
    out.remote_id_tx_ua_type = in.remote_id_tx_ua_type;
    memcpy(out.remote_id_tx_uas_id, in.remote_id_tx_uas_id, sizeof(in.remote_id_tx_uas_id));
    memcpy(out.remote_id_tx_operator_id, in.remote_id_tx_operator_id, sizeof(in.remote_id_tx_operator_id));

    memcpy(out.feed_uris, in.feed_uris, sizeof(in.feed_uris));
    memcpy(out.feed_ports, in.feed_ports, sizeof(in.feed_ports));
    memcpy(out.feed_is_active, in.feed_is_active, sizeof(in.feed_is_active));
    for (uint16_t i = 0; i < settings_v17::kMaxNumFeeds; i++) {
        out.feed_protocols[i] = in.feed_protocols[i];
    }
    memcpy(out.feed_receiver_ids, in.feed_receiver_ids, sizeof(in.feed_receiver_ids));

    out.mavlink_system_id = in.mavlink_system_id;
    out.mavlink_component_id = in.mavlink_component_id;

    memcpy(&out.rx_position, &in.rx_position, sizeof(in.rx_position));
    out.ip_mode = in.ip_mode;
}

void SettingsMigrator::MigrateV17ToV18(const settings_v17::Settings& in, settings_v18::Settings& out) {
    // v18 only adds auto_update_enabled in v17's tail padding; it starts off.
    memcpy(&out, &in, sizeof(in));
    out.settings_version = 18;
    out.auto_update_enabled = false;
}

void SettingsMigrator::MigrateV18ToV19(const settings_v18::Settings& in, settings_v19::Settings& out) {
    // v19 appends feed transports and MQTT options after v18's fields: every feed keeps the TCP transport (0).
    memset(&out, 0, sizeof(out));
    memcpy(&out, &in, offsetof(settings_v19::Settings, feed_transports));
    out.settings_version = 19;
}

void SettingsMigrator::MigrateV19ToV20(const settings_v19::Settings& in, settings_v20::Settings& out) {
    // v20 appends the ASTERIX SAC/SIC (0, 0) and the NTP server (pool.ntp.org) after v19's fields.
    memset(&out, 0, sizeof(out));
    memcpy(&out, &in, offsetof(settings_v20::Settings, asterix_sac));
    out.settings_version = 20;
    strncpy(out.ntp_server, "pool.ntp.org", settings_v20::kNTPServerMaxLen);
}

void SettingsMigrator::MigrateV20ToV21(const settings_v20::Settings& in, SettingsManager::Settings& out) {
    // Start from a fresh, fully-defaulted current struct: the fixed antenna position (new in v21) starts unset.
    out = SettingsManager::Settings();

    out.settings_version = kSettingsVersion;

    memcpy(&out.core_network_settings, &in.core_network_settings, sizeof(in.core_network_settings));

    out.r1090_rx_enabled = in.r1090_rx_enabled;
    out.tl_offset_mv = in.tl_offset_mv;
    out.r1090_bias_tee_enabled = in.r1090_bias_tee_enabled;
    out.watchdog_timeout_sec = in.watchdog_timeout_sec;
    out.led_enabled = in.led_enabled;
    out.feeds_enabled = in.feeds_enabled;
    out.gnss_enabled = in.gnss_enabled;
    out.gnss_receiver_type = static_cast<SettingsManager::GNSSReceiverType>(in.gnss_receiver_type);
    out.gnss_notify = in.gnss_notify;

    out.log_level = static_cast<SettingsManager::LogLevel>(in.log_level);
    for (uint16_t i = 0; i < SettingsManager::SerialInterface::kNumSerialInterfaces; i++) {
        out.reporting_protocols[i] = static_cast<SettingsManager::ReportingProtocol>(in.reporting_protocols[i]);
        out.baud_rates[i] = in.baud_rates[i];
    }

    out.subg_enabled = static_cast<SettingsManager::EnableState>(in.subg_enabled);
    out.subg_rx_enabled = in.subg_rx_enabled;
    out.subg_bias_tee_enabled = in.subg_bias_tee_enabled;
    out.subg_mode = static_cast<SettingsManager::SubGHzRadioMode>(in.subg_mode);

    out.remote_id_rx_enabled = in.remote_id_rx_enabled;
    out.remote_id_transports = in.remote_id_transports;

    out.remote_id_tx_enabled = in.remote_id_tx_enabled;
    out.remote_id_tx_transports = in.remote_id_tx_transports;
    out.remote_id_tx_uas_id_type = in.remote_id_tx_uas_id_type;
    out.remote_id_tx_ua_type = in.remote_id_tx_ua_type;
    memcpy(out.remote_id_tx_uas_id, in.remote_id_tx_uas_id, sizeof(in.remote_id_tx_uas_id));
    memcpy(out.remote_id_tx_operator_id, in.remote_id_tx_operator_id, sizeof(in.remote_id_tx_operator_id));

    memcpy(out.feed_uris, in.feed_uris, sizeof(in.feed_uris));
    memcpy(out.feed_ports, in.feed_ports, sizeof(in.feed_ports));
    memcpy(out.feed_is_active, in.feed_is_active, sizeof(in.feed_is_active));
    for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
        out.feed_protocols[i] = static_cast<SettingsManager::ReportingProtocol>(in.feed_protocols[i]);
    }
    memcpy(out.feed_receiver_ids, in.feed_receiver_ids, sizeof(in.feed_receiver_ids));

    out.mavlink_system_id = in.mavlink_system_id;
    out.mavlink_component_id = in.mavlink_component_id;

    memcpy(&out.rx_position, &in.rx_position, sizeof(in.rx_position));
    out.ip_mode = static_cast<SettingsManager::IPMode>(in.ip_mode);
    memcpy(out.wifi_sta_extra_networks, in.wifi_sta_extra_networks, sizeof(in.wifi_sta_extra_networks));
    out.auto_update_enabled = in.auto_update_enabled;
    for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
        out.feed_transports[i] = static_cast<SettingsManager::FeedTransport>(in.feed_transports[i]);
    }
    memcpy(out.feed_mqtt, in.feed_mqtt, sizeof(in.feed_mqtt));
    out.asterix_sac = in.asterix_sac;
    out.asterix_sic = in.asterix_sic;
    memcpy(out.ntp_server, in.ntp_server, sizeof(in.ntp_server));
}

bool SettingsMigrator::Migrate(const uint8_t* blob, uint16_t blob_len, uint32_t from_version,
                               SettingsManager::Settings& out) {
    // Each case enters the chain at its own version and falls through the remaining one-step upgrades to reach the
    // current version, so any stored version >= kOldestMigratableVersion lands on the live layout.
    settings_v13::Settings v13;
    settings_v14::Settings v14;
    settings_v15::Settings v15;
    settings_v16::Settings v16;
    static settings_v17::Settings v17;  // Static: the snapshots above already fill the RP2040's 4 kB stack.
    static settings_v18::Settings v18;
    static settings_v19::Settings v19;
    static settings_v20::Settings v20;

    switch (from_version) {
        case 12: {
            if (blob_len < sizeof(settings_v12::Settings)) {
                return false;  // Stored blob too short to be a valid v12 struct.
            }
            // Copy into a properly-aligned local rather than reinterpret_cast'ing the (possibly-unaligned) blob.
            settings_v12::Settings v12;
            memcpy(&v12, blob, sizeof(v12));
            MigrateV12ToV13(v12, v13);
            MigrateV13ToV14(v13, v14);
            MigrateV14ToV15(v14, v15);
            MigrateV15ToV16(v15, v16);
            break;
        }
        case 13: {
            if (blob_len < sizeof(settings_v13::Settings)) {
                return false;
            }
            memcpy(&v13, blob, sizeof(v13));
            MigrateV13ToV14(v13, v14);
            MigrateV14ToV15(v14, v15);
            MigrateV15ToV16(v15, v16);
            break;
        }
        case 14: {
            if (blob_len < sizeof(settings_v14::Settings)) {
                return false;
            }
            memcpy(&v14, blob, sizeof(v14));
            MigrateV14ToV15(v14, v15);
            MigrateV15ToV16(v15, v16);
            break;
        }
        case 15: {
            if (blob_len < sizeof(settings_v15::Settings)) {
                return false;
            }
            memcpy(&v15, blob, sizeof(v15));
            MigrateV15ToV16(v15, v16);
            break;
        }
        case 16: {
            if (blob_len < sizeof(settings_v16::Settings)) {
                return false;
            }
            memcpy(&v16, blob, sizeof(v16));
            break;
        }
        case 17: {
            if (blob_len < sizeof(settings_v17::Settings)) {
                return false;
            }
            memcpy(&v17, blob, sizeof(v17));
            MigrateV17ToV18(v17, v18);
            MigrateV18ToV19(v18, v19);
            MigrateV19ToV20(v19, v20);
            MigrateV20ToV21(v20, out);
            return true;
        }
        case 18: {
            if (blob_len < sizeof(settings_v18::Settings)) {
                return false;
            }
            memcpy(&v18, blob, sizeof(v18));
            MigrateV18ToV19(v18, v19);
            MigrateV19ToV20(v19, v20);
            MigrateV20ToV21(v20, out);
            return true;
        }
        case 19: {
            if (blob_len < sizeof(settings_v19::Settings)) {
                return false;
            }
            memcpy(&v19, blob, sizeof(v19));
            MigrateV19ToV20(v19, v20);
            MigrateV20ToV21(v20, out);
            return true;
        }
        case 20: {
            if (blob_len < sizeof(settings_v20::Settings)) {
                return false;
            }
            memcpy(&v20, blob, sizeof(v20));
            MigrateV20ToV21(v20, out);
            return true;
        }
        default:
            // Older than kOldestMigratableVersion, unknown, or already current: nothing to migrate.
            return false;
    }

    MigrateV16ToV17(v16, v17);
    MigrateV17ToV18(v17, v18);
    MigrateV18ToV19(v18, v19);
    MigrateV19ToV20(v19, v20);
    MigrateV20ToV21(v20, out);  // Final step: v20 is the newest frozen version, so this lands on the live struct.
    return true;
}
