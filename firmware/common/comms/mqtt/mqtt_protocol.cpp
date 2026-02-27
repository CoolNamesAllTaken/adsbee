#include "mqtt_protocol.hh"
#include <stdio.h>
#include <string.h>

// Main formatting functions
uint16_t MQTTProtocol::FormatPacket(const DecodedModeSPacket& packet,
                                     uint8_t* buffer,
                                     uint16_t buffer_size,
                                     Format format,
                                     TransponderProtocol protocol) {
    if (!buffer || buffer_size < 20) {
        fprintf(stderr, "MQTTProtocol::FormatPacket: Invalid buffer (%p) or size (%u).\n",
                (void*)buffer, buffer_size);
        return 0;
    }

    if (format == kFormatJSON) {
        return FormatPacketJSON(packet, (char*)buffer, buffer_size, protocol);
    } else {
        return FormatPacketBinary(packet, buffer, buffer_size, protocol);
    }
}

uint16_t MQTTProtocol::FormatUATPacket(const DecodedUATADSBPacket& packet,
                                       uint8_t* buffer,
                                       uint16_t buffer_size,
                                       Format format) {
    if (!buffer || buffer_size < 20) {
        fprintf(stderr, "MQTTProtocol::FormatUATPacket: Invalid buffer (%p) or size (%u).\n",
                (void*)buffer, buffer_size);
        return 0;
    }

    if (format == kFormatJSON) {
        return FormatUATPacketJSON(packet, (char*)buffer, buffer_size);
    } else {
        return FormatUATPacketBinary(packet, buffer, buffer_size);
    }
}

uint16_t MQTTProtocol::FormatAircraft(const ModeSAircraft& aircraft,
                                       uint8_t* buffer,
                                       uint16_t buffer_size,
                                       Format format,
                                       TransponderProtocol protocol) {
    if (!buffer || buffer_size < 20) {
        fprintf(stderr, "MQTTProtocol::FormatAircraft: Invalid buffer (%p) or size (%u).\n",
                (void*)buffer, buffer_size);
        return 0;
    }

    if (format == kFormatJSON) {
        return FormatAircraftJSON(aircraft, (char*)buffer, buffer_size, protocol);
    } else {
        return FormatAircraftBinary(aircraft, buffer, buffer_size, protocol);
    }
}

bool MQTTProtocol::GetTopic(uint32_t icao24,
                            const char* msg_type,
                            char* topic_buf,
                            uint16_t topic_size,
                            TransponderProtocol protocol,
                            bool use_short,
                            const char* device_id) {
    if (!topic_buf || !msg_type || topic_size < 16) {
        return false;
    }

    int written;
    const char* protocol_str = (protocol == kUAT) ? "uat" : "adsb";
    const char* protocol_short = (protocol == kUAT) ? "u" : "a";

    if (device_id && strlen(device_id) > 0) {
        // Include device ID in topic hierarchy
        if (use_short) {
            // Short topics for binary format
            const char* short_type = "x";
            if (strcmp(msg_type, "position") == 0) short_type = "p";
            else if (strcmp(msg_type, "status") == 0) short_type = "s";
            else if (strcmp(msg_type, "raw") == 0) short_type = "r";

            written = snprintf(topic_buf, topic_size, "%s/%s/%06X/%s",
                             device_id, protocol_short, (unsigned int)icao24, short_type);
        } else {
            // Standard topics for JSON
            written = snprintf(topic_buf, topic_size, "%s/%s/%06X/%s",
                             device_id, protocol_str, (unsigned int)icao24, msg_type);
        }
    } else {
        // No device ID - use original format for backward compatibility
        if (use_short) {
            const char* short_type = "x";
            if (strcmp(msg_type, "position") == 0) short_type = "p";
            else if (strcmp(msg_type, "status") == 0) short_type = "s";
            else if (strcmp(msg_type, "raw") == 0) short_type = "r";

            written = snprintf(topic_buf, topic_size, "%s/%06X/%s",
                             protocol_short, (unsigned int)icao24, short_type);
        } else {
            written = snprintf(topic_buf, topic_size, "%s/%06X/%s",
                             protocol_str, (unsigned int)icao24, msg_type);
        }
    }

    return (written > 0 && written < topic_size);
}

// JSON Implementation
uint16_t MQTTProtocol::FormatPacketJSON(const DecodedModeSPacket& packet,
                                         char* buffer,
                                         uint16_t buffer_size,
                                         TransponderProtocol protocol) {
    uint32_t icao24 = packet.icao_address;
    uint8_t df = packet.downlink_format;
    const char* protocol_str = (protocol == kUAT) ? "UAT" : "1090";

    // Build JSON with essential fields including protocol
    int written = snprintf(buffer, buffer_size,
        "{\"t\":%llu,"           // timestamp (short key)
        "\"icao\":\"%06X\","
        "\"band\":\"%s\","       // Transponder protocol
        "\"df\":%d,"
        "\"rssi\":%d,"
        "\"hex\":\"",
        (unsigned long long)(packet.raw.GetMLAT12MHzCounter() / 12000),  // Convert to ms
        (unsigned int)icao24,
        protocol_str,
        df,
        packet.raw.sigs_dbm
    );

    if (written < 0 || written >= buffer_size) {
        return 0;
    }

    // Add hex data
    char* ptr = buffer + written;
    int remaining = buffer_size - written;

    uint32_t packet_buf[DecodedModeSPacket::kMaxPacketLenWords32];
    uint16_t packet_len_bytes = packet.DumpPacketBuffer(packet_buf);
    uint8_t* packet_bytes = (uint8_t*)packet_buf;

    for (int i = 0; i < packet_len_bytes && remaining > 3; i++) {
        int n = snprintf(ptr, remaining, "%02X", packet_bytes[i]);
        if (n < 0 || n >= remaining) break;
        ptr += n;
        remaining -= n;
        written += n;
    }

    // Close JSON
    int n = snprintf(ptr, remaining, "\"}");
    if (n < 0 || n >= remaining) {
        return 0;
    }

    return written + n;
}

uint16_t MQTTProtocol::FormatAircraftJSON(const ModeSAircraft& aircraft,
                                           char* buffer,
                                           uint16_t buffer_size,
                                           TransponderProtocol protocol) {
    const char* protocol_str = (protocol == kUAT) ? "UAT" : "1090";

    // Compact JSON with short keys including protocol and category code
    int written = snprintf(buffer, buffer_size,
        "{\"t\":%lu,"        // Timestamp (ms since boot) of last decode
        "\"icao\":\"%06X\","
        "\"band\":\"%s\","   // Transponder protocol
        "\"call\":\"%s\","
        "\"cat\":\"%s\","    // Aircraft category code (e.g., A3, C1)
        "\"lat\":%.5f,"      // 5 decimal places sufficient
        "\"lon\":%.5f,"
        "\"alt\":%d,"        // Barometric altitude in feet
        "\"hdg\":%.0f,"      // No decimals for heading
        "\"spd\":%d,"        // Speed in knots (int32_t)
        "\"vr\":%d,"         // Vertical rate
        "\"sqk\":\"%04X\","
        "\"gnd\":%d}",       // 1/0 instead of true/false
        (unsigned long)aircraft.last_message_timestamp_ms,
        (unsigned int)aircraft.icao_address,
        protocol_str,
        aircraft.callsign,
        ADSBTypes::GetCategoryCode(aircraft.emitter_category_raw),  // Use standard category code
        aircraft.latitude_deg,
        aircraft.longitude_deg,
        (int)aircraft.baro_altitude_ft,
        aircraft.direction_deg,
        (int)aircraft.speed_kts,
        (int)aircraft.baro_vertical_rate_fpm,
        aircraft.squawk,
        (aircraft.flags & (1 << ModeSAircraft::kBitFlagIsAirborne)) ? 0 : 1
    );

    if (written < 0 || written >= buffer_size) {
        return 0;
    }

    return written;
}

// Binary Implementation
uint16_t MQTTProtocol::FormatPacketBinary(const DecodedModeSPacket& packet,
                                           uint8_t* buffer,
                                           uint16_t buffer_size,
                                           TransponderProtocol protocol) {
    uint8_t df = packet.downlink_format;
    uint8_t len = (df >= 16) ? 14 : 7;  // Long or short format

    if (buffer_size < len + 2) {
        return 0;
    }

    // Format: [Type:1][Protocol:2bits|Reserved:6bits][Data:7-14]
    buffer[0] = kBinaryRaw;
    buffer[1] = (protocol & 0x03) << 6;  // Protocol in upper 2 bits
    uint32_t packet_buf[DecodedModeSPacket::kMaxPacketLenWords32];
    packet.DumpPacketBuffer(packet_buf);
    memcpy(buffer + 2, packet_buf, len);

    return len + 2;
}

// UAT Implementation
uint16_t MQTTProtocol::FormatUATPacketJSON(const DecodedUATADSBPacket& packet,
                                            char* buffer,
                                            uint16_t buffer_size) {
    uint32_t icao24 = packet.GetICAOAddress();

    // Build JSON with essential fields
    int written = snprintf(buffer, buffer_size,
        "{\"t\":%llu,"           // timestamp (short key)
        "\"icao\":\"%06X\","
        "\"band\":\"UAT\","
        "\"rssi\":%d,"
        "\"hex\":\"",
        (unsigned long long)(packet.raw.GetMLAT12MHzCounter() / 12000),  // Convert to ms
        (unsigned int)icao24,
        packet.raw.sigs_dbm
    );

    if (written < 0 || written >= buffer_size) {
        return 0;
    }

    // Add hex data
    char* ptr = buffer + written;
    int remaining = buffer_size - written;

    for (uint16_t i = 0; i < packet.raw.buffer_len_bytes && remaining > 3; i++) {
        int n = snprintf(ptr, remaining, "%02X", packet.raw.buffer[i]);
        if (n < 0 || n >= remaining) break;
        ptr += n;
        remaining -= n;
        written += n;
    }

    // Close JSON
    int n = snprintf(ptr, remaining, "\"}");
    if (n < 0 || n >= remaining) {
        return 0;
    }

    return written + n;
}

uint16_t MQTTProtocol::FormatUATPacketBinary(const DecodedUATADSBPacket& packet,
                                              uint8_t* buffer,
                                              uint16_t buffer_size) {
    uint16_t len = packet.raw.buffer_len_bytes;

    if (buffer_size < len + 2 || len == 0) {
        return 0;
    }

    // Format: [Type:1][Protocol:2bits|Reserved:6bits][Data:variable]
    buffer[0] = kBinaryRaw;
    buffer[1] = (kUAT & 0x03) << 6;  // Protocol in upper 2 bits
    memcpy(buffer + 2, packet.raw.buffer, len);

    return len + 2;
}

uint16_t MQTTProtocol::FormatAircraftBinary(const ModeSAircraft& aircraft,
                                             uint8_t* buffer,
                                             uint16_t buffer_size,
                                             TransponderProtocol protocol) {
    if (buffer_size < sizeof(BinaryAircraft)) {
        return 0;
    }

    BinaryAircraft* msg = (BinaryAircraft*)buffer;

    // Pack all data into compact structure
    msg->type = kBinaryAircraft;
    msg->protocol = protocol & 0x03;  // 2-bit protocol identifier
    msg->icao24 = aircraft.icao_address & 0xFFFFFF;
    msg->rssi = (aircraft.last_message_signal_strength_dbm + 63) & 0x3F;  // Convert to 6-bit value
    msg->timestamp_s = (aircraft.last_message_timestamp_ms / 1000) & 0xFFFF;

    // Fixed-point encoding for lat/lon (0.00001 degree precision)
    msg->latitude_deg_e5 = (int32_t)(aircraft.latitude_deg * 100000) & 0xFFFFFF;
    msg->longitude_deg_e5 = (int32_t)(aircraft.longitude_deg * 100000) & 0xFFFFFF;

    // Altitude in 25ft increments (up to 1.6M ft)
    msg->altitude_25ft = aircraft.baro_altitude_ft / 25;

    // Pack other fields
    msg->heading_deg = (uint16_t)aircraft.direction_deg & 0x1FF;
    msg->speed_kts = (uint16_t)aircraft.speed_kts & 0x3FF;
    msg->vertical_rate_64fpm = aircraft.baro_vertical_rate_fpm / 64;  // 64 fpm increments

    // Status flags
    msg->flags = 0;
    if (!(aircraft.flags & (1 << ModeSAircraft::kBitFlagIsAirborne))) msg->flags |= 0x01;  // On ground
    if (aircraft.flags & (1 << ModeSAircraft::kBitFlagAlert)) msg->flags |= 0x02;
    if (aircraft.flags & (1 << ModeSAircraft::kBitFlagIdent)) msg->flags |= 0x04;  // Using Ident for emergency
    if (aircraft.flags & (1 << ModeSAircraft::kBitFlagTCASRA)) msg->flags |= 0x08;  // TCAS RA

    // Add raw category code (includes both CA and TYPE)
    msg->category = aircraft.emitter_category_raw;

    // Add callsign (8 bytes, null padded)
    memset(msg->callsign, 0, 8);
    strncpy((char*)msg->callsign, aircraft.callsign, 8);

    return sizeof(BinaryAircraft);
}

// Telemetry formatting
uint16_t MQTTProtocol::FormatTelemetry(const TelemetryData& telemetry,
                                        uint8_t* buffer,
                                        uint16_t buffer_size,
                                        Format format) {
    if (!buffer || buffer_size < 20) {
        fprintf(stderr, "MQTTProtocol::FormatTelemetry: Invalid buffer (%p) or size (%u).\n",
                (void*)buffer, buffer_size);
        return 0;
    }

    if (format == kFormatJSON) {
        return FormatTelemetryJSON(telemetry, (char*)buffer, buffer_size);
    } else {
        return FormatTelemetryBinary(telemetry, buffer, buffer_size);
    }
}

uint16_t MQTTProtocol::FormatTelemetryJSON(const TelemetryData& telemetry,
                                            char* buffer,
                                            uint16_t buffer_size) {
    // Build firmware version string: include RC suffix only for release candidates.
    char fw_ver_str[24];
    if (telemetry.fw_rc > 0) {
        snprintf(fw_ver_str, sizeof(fw_ver_str), "%u.%u.%u-rc%u",
                 telemetry.fw_major, telemetry.fw_minor, telemetry.fw_patch, telemetry.fw_rc);
    } else {
        snprintf(fw_ver_str, sizeof(fw_ver_str), "%u.%u.%u",
                 telemetry.fw_major, telemetry.fw_minor, telemetry.fw_patch);
    }

    int written = snprintf(buffer, buffer_size,
        "{\"uptime\":%lu,"
        "\"msgs_adsb_ps\":%u,"
        "\"msgs_mqtt_tx\":%u,"
        "\"esp_temp\":%d,"
        "\"pico_temp\":%d,"
        "\"pico_cpu\":[%u,%u],"
        "\"aircraft\":%u,"
        "\"mem_free\":%u,"
        "\"noise_floor\":%d,"
        "\"rx_1090\":%d,"
        "\"rx_subg\":%d,"
        "\"wifi\":%d,"
        "\"mqtt\":%d,"
        "\"fw_ver\":\"%s\"",
        telemetry.uptime_sec,
        telemetry.messages_received,
        telemetry.messages_sent,
        telemetry.cpu_temp_c,
        telemetry.pico_temp_c,
        telemetry.pico_core0_pct,
        telemetry.pico_core1_pct,
        telemetry.aircraft_count,
        telemetry.memory_free_kb,
        telemetry.rssi_noise_floor_dbm,
        telemetry.receiver_1090_enabled,
        telemetry.receiver_subg_enabled,
        telemetry.wifi_connected,
        telemetry.mqtt_connected,
        fw_ver_str
    );

    if (written < 0 || written >= buffer_size) {
        return 0;
    }

    // Append message rate info if present
    int remaining = buffer_size - written;
    char* ptr = buffer + written;

    if (telemetry.mps_feed_count > 0 || telemetry.mps_total > 0) {
        int n = snprintf(ptr, remaining, ",\"mps_total\":%u,\"mps\":[",
                         telemetry.mps_total);
        if (n < 0 || n >= remaining) return 0;
        ptr += n; remaining -= n; written += n;

        for (uint8_t i = 0; i < telemetry.mps_feed_count && i < TelemetryData::kMaxFeedsForTelemetry; i++) {
            n = snprintf(ptr, remaining, "%s%u", (i == 0 ? "" : ","), telemetry.mps_feeds[i]);
            if (n < 0 || n >= remaining) return 0;
            ptr += n; remaining -= n; written += n;
        }
        n = snprintf(ptr, remaining, "]");
        if (n < 0 || n >= remaining) return 0;
        ptr += n; remaining -= n; written += n;
    }

    int n = snprintf(ptr, remaining, "}");
    if (n < 0 || n >= remaining) return 0;
    written += n;

    return written;
}

uint16_t MQTTProtocol::FormatTelemetryBinary(const TelemetryData& telemetry,
                                              uint8_t* buffer,
                                              uint16_t buffer_size) {
    if (buffer_size < sizeof(BinaryTelemetry)) {
        return 0;
    }

    BinaryTelemetry* msg = (BinaryTelemetry*)buffer;

    msg->type = kBinaryTelemetry;
    msg->uptime_min = (telemetry.uptime_sec / 60) & 0xFFFFFF;  // Minutes
    msg->msgs_rx_count = telemetry.messages_received;
    msg->msgs_tx_count = telemetry.messages_sent;
    msg->cpu_temp_c = telemetry.cpu_temp_c;
    msg->mem_free_mb = telemetry.memory_free_kb / 1024;  // Convert to MB
    msg->noise_floor_dbm = telemetry.rssi_noise_floor_dbm;

    // Pack status bits
    msg->status = 0;
    if (telemetry.receiver_1090_enabled) msg->status |= 0x01;
    if (telemetry.receiver_subg_enabled) msg->status |= 0x02;
    if (telemetry.wifi_connected) msg->status |= 0x04;
    if (telemetry.mqtt_connected) msg->status |= 0x08;

    msg->reserved[0] = 0;
    msg->reserved[1] = 0;

    return sizeof(BinaryTelemetry);
}

// GNSS formatting
uint16_t MQTTProtocol::FormatGNSS(const GNSSData& gnss,
                                    uint8_t* buffer,
                                    uint16_t buffer_size,
                                    Format format) {
    if (!buffer || buffer_size < 15) {
        fprintf(stderr, "MQTTProtocol::FormatGNSS: Invalid buffer (%p) or size (%u).\n",
                (void*)buffer, buffer_size);
        return 0;
    }

    if (format == kFormatJSON) {
        return FormatGNSSJSON(gnss, (char*)buffer, buffer_size);
    } else {
        return FormatGNSSBinary(gnss, buffer, buffer_size);
    }
}

uint16_t MQTTProtocol::FormatGNSSJSON(const GNSSData& gnss,
                                       char* buffer,
                                       uint16_t buffer_size) {
    const char* fix_str = (gnss.fix_status == 2) ? "3D" :
                         (gnss.fix_status == 1) ? "2D" : "None";

    int written = snprintf(buffer, buffer_size,
        "{\"lat_deg\":%.6f,"
        "\"lon_deg\":%.6f,"
        "\"alt_m\":%.1f,"
        "\"fix\":\"%s\","
        "\"sats\":%u,"
        "\"hdop\":%.2f,"
        "\"ts\":%lu}",
        gnss.latitude_deg,
        gnss.longitude_deg,
        gnss.altitude_m,
        fix_str,
        gnss.num_satellites,
        gnss.hdop,
        gnss.timestamp_s
    );

    if (written < 0 || written >= buffer_size) {
        return 0;
    }

    return written;
}

uint16_t MQTTProtocol::FormatGNSSBinary(const GNSSData& gnss,
                                         uint8_t* buffer,
                                         uint16_t buffer_size) {
    if (buffer_size < sizeof(BinaryGNSS)) {
        return 0;
    }

    BinaryGNSS* msg = (BinaryGNSS*)buffer;

    msg->type = kBinaryGNSS;
    msg->latitude_deg_e5 = (int32_t)(gnss.latitude_deg * 100000) & 0xFFFFFF;
    msg->longitude_deg_e5 = (int32_t)(gnss.longitude_deg * 100000) & 0xFFFFFF;
    msg->altitude_m = (uint16_t)gnss.altitude_m;
    msg->fix = gnss.fix_status & 0x03;
    msg->sats = gnss.num_satellites & 0x3F;
    msg->hdop_e2 = (uint16_t)(gnss.hdop * 100);
    msg->timestamp_min = (gnss.timestamp_s / 60) & 0xFFFF;  // Minutes since epoch

    return sizeof(BinaryGNSS);
}

bool MQTTProtocol::GetTelemetryTopic(char* topic_buf,
                                     uint16_t topic_size,
                                     const char* msg_type,
                                     bool use_short,
                                     const char* device_id) {
    if (!topic_buf || !msg_type || topic_size < 16) {
        return false;
    }

    int written;

    if (device_id && strlen(device_id) > 0) {
        // Include device ID in topic hierarchy
        if (use_short) {
            // Short topics for binary format
            const char* short_type = "x";
            if (strcmp(msg_type, "telemetry") == 0) short_type = "t";
            else if (strcmp(msg_type, "position") == 0) short_type = "g";

            written = snprintf(topic_buf, topic_size, "%s/sys/%s", device_id, short_type);
        } else {
            // Standard topics for JSON
            written = snprintf(topic_buf, topic_size, "%s/system/%s", device_id, msg_type);
        }
    } else {
        // No device ID - use original format for backward compatibility
        if (use_short) {
            const char* short_type = "x";
            if (strcmp(msg_type, "telemetry") == 0) short_type = "t";
            else if (strcmp(msg_type, "position") == 0) short_type = "g";

            written = snprintf(topic_buf, topic_size, "sys/%s", short_type);
        } else {
            written = snprintf(topic_buf, topic_size, "system/%s", msg_type);
        }
    }

    return (written > 0 && written < topic_size);
}
