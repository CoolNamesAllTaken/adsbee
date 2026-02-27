#pragma once

#include <stdint.h>
#include <string.h>
#include "mode_s_packet.hh"
#include "uat_packet.hh"
#include "data_structures.hh"
#include "aircraft_dictionary.hh"

/**
 * MQTT protocol formatter for ADS-B data.
 * Supports both JSON (human-readable) and binary (bandwidth-optimized) formats.
 * Prioritizes real-time delivery - no batching delays.
 */

class MQTTProtocol {
public:
    // Output format selection
    enum Format : uint8_t {
        kFormatJSON = 0,    // Human-readable JSON (~250 bytes/msg)
        kFormatBinary = 1   // Compact binary (~20 bytes/msg)
    };

    // Binary message types
    enum BinaryType : uint8_t {
        kBinaryPosition = 0x01,   // Position update (13 bytes)
        kBinaryAircraft = 0x02,   // Full aircraft state (20 bytes)
        kBinaryRaw = 0x03,        // Raw Mode-S packet (8-15 bytes)
        kBinaryTelemetry = 0x04,  // Device telemetry (variable)
        kBinaryGNSS = 0x05        // GNSS status (15 bytes)
    };

    // Transponder protocol source
    enum TransponderProtocol : uint8_t {
        kModeS = 0,       // Mode S / ADS-B (1090 MHz)
        kUAT = 1,         // UAT (978 MHz)
        kUnknown = 2      // Unknown source
    };

    // Compact binary structure for aircraft data (23 bytes total)
    struct __attribute__((packed)) BinaryAircraft {
        uint8_t type;             // Message type (1 byte)
        uint8_t protocol : 2;    // Transponder protocol (2 bits)
        uint32_t icao24 : 24;    // ICAO address (3 bytes)
        uint8_t rssi : 6;        // Signal strength (6 bits, -63 to 0 dBm)
        uint16_t timestamp_s;    // Seconds since epoch % 65536 (2 bytes)
        int32_t latitude_deg_e5 : 24;   // Latitude * 1e5 (3 bytes)
        int32_t longitude_deg_e5 : 24;  // Longitude * 1e5 (3 bytes)
        uint16_t altitude_25ft;  // Altitude in 25ft units (2 bytes)
        uint16_t heading_deg : 9;       // Heading 0-359 degrees (9 bits)
        uint16_t speed_kts : 10;        // Speed in knots (10 bits)
        int16_t vertical_rate_64fpm : 13; // Vertical rate / 64 fpm (13 bits)
        uint8_t flags;            // Status flags (1 byte)
        uint8_t category;         // Aircraft category (1 byte)
        uint8_t callsign[8];     // Callsign (8 bytes, null padded)
    };

    // Telemetry data structure
    struct TelemetryData {
        uint32_t uptime_sec;           // Uptime in seconds
        uint16_t messages_received;    // ADS-B messages per second (published/decoded)
        uint16_t messages_sent;        // MQTT messages sent (cumulative)
        int16_t cpu_temp_c;           // ESP32 CPU temperature (Celsius)
        uint16_t memory_free_kb;      // ESP32 free memory in KB
        int16_t rssi_noise_floor_dbm; // Current noise floor
        uint8_t receiver_1090_enabled; // 1090 MHz receiver status
        uint8_t receiver_subg_enabled; // Sub-GHz receiver status (UAT, ADS-L, FLARM)
        uint8_t wifi_connected;        // WiFi connection status
        uint8_t mqtt_connected;        // MQTT connection status
        // Firmware version info
        uint8_t fw_major = 0;          // Firmware major version
        uint8_t fw_minor = 0;          // Firmware minor version
        uint8_t fw_patch = 0;          // Firmware patch version
        uint8_t fw_rc = 0;             // Firmware release candidate version
        // RP2040 metrics
        int16_t pico_temp_c = 0;       // RP2040 CPU temperature (Celsius)
        uint8_t pico_core0_pct = 0;    // RP2040 core 0 usage percent
        uint8_t pico_core1_pct = 0;    // RP2040 core 1 usage percent
        // Aircraft tracking
        uint16_t aircraft_count = 0;   // Number of tracked aircraft
        // Optional message rate reporting (JSON only)
        uint16_t mps_total = 0;        // Total messages per second across all feeds
        uint8_t mps_feed_count = 0;    // Number of per-feed entries populated in mps_feeds
        static constexpr uint8_t kMaxFeedsForTelemetry = 10;
        uint16_t mps_feeds[kMaxFeedsForTelemetry] = {0}; // Per-feed messages per second
    };

    // GNSS data structure
    struct GNSSData {
        double latitude_deg;       // Receiver latitude in degrees
        double longitude_deg;      // Receiver longitude in degrees
        float altitude_m;          // Altitude in meters
        uint8_t fix_status;        // 0=no fix, 1=2D, 2=3D
        uint8_t num_satellites;    // Number of satellites
        float hdop;                // Horizontal dilution of precision
        uint32_t timestamp_s;      // GNSS timestamp in seconds
    };

    // Compact binary telemetry (16 bytes)
    struct __attribute__((packed)) BinaryTelemetry {
        uint8_t type;                       // Message type (kBinaryTelemetry)
        uint32_t uptime_min : 24;           // Uptime in minutes (3 bytes)
        uint16_t msgs_rx_count;             // Messages received (2 bytes)
        uint16_t msgs_tx_count;             // Messages transmitted (2 bytes)
        int8_t cpu_temp_c;                  // CPU temp in Celsius (1 byte)
        uint16_t mem_free_mb;               // Free memory in MB (2 bytes)
        int8_t noise_floor_dbm;             // Noise floor in dBm (1 byte)
        uint8_t status;                     // Status bits (1 byte)
        uint8_t reserved[2];               // Reserved for future use
    };

    // Compact binary GNSS (15 bytes)
    struct __attribute__((packed)) BinaryGNSS {
        uint8_t type;                       // Message type (kBinaryGNSS)
        int32_t latitude_deg_e5 : 24;      // Latitude * 1e5 (3 bytes)
        int32_t longitude_deg_e5 : 24;     // Longitude * 1e5 (3 bytes)
        uint16_t altitude_m;               // Altitude in meters (2 bytes)
        uint8_t fix : 2;                   // Fix status (2 bits)
        uint8_t sats : 6;                  // Number of satellites (6 bits)
        uint16_t hdop_e2;                  // HDOP * 100 (2 bytes)
        uint16_t timestamp_min;            // Minutes since epoch % 65536 (2 bytes)
    };

    static const uint16_t kMaxMessageSize = 512;  // Max size for any message
    static const uint16_t kMaxTopicSize = 64;     // Max MQTT topic length

    /**
     * Format a decoded ADS-B packet for MQTT publishing
     * @param[in] packet The decoded packet
     * @param[out] buffer Output buffer
     * @param[in] buffer_size Buffer size
     * @param[in] format Output format (JSON or BINARY)
     * @param[in] protocol Transponder protocol source
     * @return Number of bytes written, 0 on error
     */
    static uint16_t FormatPacket(const DecodedModeSPacket& packet,
                                  uint8_t* buffer,
                                  uint16_t buffer_size,
                                  Format format,
                                  TransponderProtocol protocol = kModeS);

    /**
     * Format a decoded UAT ADS-B packet for MQTT publishing
     * @param[in] packet The decoded UAT packet
     * @param[out] buffer Output buffer
     * @param[in] buffer_size Buffer size
     * @param[in] format Output format (JSON or BINARY)
     * @return Number of bytes written, 0 on error
     */
    static uint16_t FormatUATPacket(const DecodedUATADSBPacket& packet,
                                     uint8_t* buffer,
                                     uint16_t buffer_size,
                                     Format format);

    /**
     * Format aircraft data for MQTT publishing
     * @param[in] aircraft The aircraft data
     * @param[out] buffer Output buffer
     * @param[in] buffer_size Buffer size
     * @param[in] format Output format (JSON or BINARY)
     * @param[in] protocol Transponder protocol source
     * @return Number of bytes written, 0 on error
     */
    static uint16_t FormatAircraft(const ModeSAircraft& aircraft,
                                    uint8_t* buffer,
                                    uint16_t buffer_size,
                                    Format format,
                                    TransponderProtocol protocol = kModeS);

    /**
     * Get MQTT topic for publishing
     * @param[in] icao24 Aircraft ICAO address
     * @param[in] msg_type Message type ("position", "status", "raw")
     * @param[out] topic_buf Buffer for topic string
     * @param[in] topic_size Buffer size
     * @param[in] protocol Transponder protocol source
     * @param[in] use_short Use short topics for binary format
     * @param[in] device_id Optional device ID to prepend to topic
     * @return true on success
     */
    static bool GetTopic(uint32_t icao24,
                        const char* msg_type,
                        char* topic_buf,
                        uint16_t topic_size,
                        TransponderProtocol protocol = kModeS,
                        bool use_short = false,
                        const char* device_id = nullptr);

    /**
     * Estimate bandwidth usage
     * @param[in] format Message format
     * @param[in] messages_per_hour Expected message rate
     * @return Estimated bytes per hour
     */
    static uint32_t EstimateBandwidth(Format format, uint16_t messages_per_hour) {
        uint16_t msg_size_bytes = (format == kFormatJSON) ? 250 : 20;
        return msg_size_bytes * messages_per_hour;
    }

    /**
     * Get format from string
     */
    static Format ParseFormat(const char* str) {
        if (str && strcasecmp(str, "BINARY") == 0) {
            return kFormatBinary;
        }
        return kFormatJSON;  // Default
    }

    /**
     * Get format string
     */
    static const char* FormatToString(Format format) {
        return (format == kFormatBinary) ? "BINARY" : "JSON";
    }

    /**
     * Format telemetry data for MQTT publishing
     * @param[in] telemetry Device telemetry data
     * @param[out] buffer Output buffer
     * @param[in] buffer_size Buffer size
     * @param[in] format Output format (JSON or BINARY)
     * @return Number of bytes written, 0 on error
     */
    static uint16_t FormatTelemetry(const TelemetryData& telemetry,
                                     uint8_t* buffer,
                                     uint16_t buffer_size,
                                     Format format);

    /**
     * Format GNSS data for MQTT publishing
     * @param[in] gnss GNSS position data
     * @param[out] buffer Output buffer
     * @param[in] buffer_size Buffer size
     * @param[in] format Output format (JSON or BINARY)
     * @return Number of bytes written, 0 on error
     */
    static uint16_t FormatGNSS(const GNSSData& gnss,
                                uint8_t* buffer,
                                uint16_t buffer_size,
                                Format format);

    /**
     * Get telemetry topic
     * @param[out] topic_buf Buffer for topic string
     * @param[in] topic_size Buffer size
     * @param[in] msg_type "telemetry" or "position"
     * @param[in] use_short Use short topics for binary format
     * @param[in] device_id Optional device ID to prepend to topic
     * @return true on success
     */
    static bool GetTelemetryTopic(char* topic_buf,
                                  uint16_t topic_size,
                                  const char* msg_type,
                                  bool use_short = false,
                                  const char* device_id = nullptr);

private:
    // JSON formatting
    static uint16_t FormatPacketJSON(const DecodedModeSPacket& packet,
                                      char* buffer,
                                      uint16_t buffer_size,
                                      TransponderProtocol protocol);

    static uint16_t FormatAircraftJSON(const ModeSAircraft& aircraft,
                                        char* buffer,
                                        uint16_t buffer_size,
                                        TransponderProtocol protocol);

    // UAT formatting
    static uint16_t FormatUATPacketJSON(const DecodedUATADSBPacket& packet,
                                         char* buffer,
                                         uint16_t buffer_size);

    static uint16_t FormatUATPacketBinary(const DecodedUATADSBPacket& packet,
                                           uint8_t* buffer,
                                           uint16_t buffer_size);

    // Binary formatting
    static uint16_t FormatPacketBinary(const DecodedModeSPacket& packet,
                                        uint8_t* buffer,
                                        uint16_t buffer_size,
                                        TransponderProtocol protocol);

    static uint16_t FormatAircraftBinary(const ModeSAircraft& aircraft,
                                          uint8_t* buffer,
                                          uint16_t buffer_size,
                                          TransponderProtocol protocol);

    // Telemetry formatting
    static uint16_t FormatTelemetryJSON(const TelemetryData& telemetry,
                                         char* buffer,
                                         uint16_t buffer_size);

    static uint16_t FormatTelemetryBinary(const TelemetryData& telemetry,
                                           uint8_t* buffer,
                                           uint16_t buffer_size);

    // GNSS formatting
    static uint16_t FormatGNSSJSON(const GNSSData& gnss,
                                    char* buffer,
                                    uint16_t buffer_size);

    static uint16_t FormatGNSSBinary(const GNSSData& gnss,
                                      uint8_t* buffer,
                                      uint16_t buffer_size);
};
