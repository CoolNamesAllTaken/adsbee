#include "gtest/gtest.h"
#include "mqtt/mqtt_protocol.hh"

// ---- Topic Generation Tests ----

TEST(MQTTProtocol, GetTopicJSON_NoBand_NoDevice) {
    char topic[MQTTProtocol::kMaxTopicSize];
    EXPECT_TRUE(MQTTProtocol::GetTopic(0xABCDEF, "raw", topic, sizeof(topic),
                                        MQTTProtocol::kModeS, false, nullptr));
    EXPECT_STREQ(topic, "adsb/ABCDEF/raw");
}

TEST(MQTTProtocol, GetTopicJSON_UAT_NoDevice) {
    char topic[MQTTProtocol::kMaxTopicSize];
    EXPECT_TRUE(MQTTProtocol::GetTopic(0x123456, "raw", topic, sizeof(topic),
                                        MQTTProtocol::kUAT, false, nullptr));
    EXPECT_STREQ(topic, "uat/123456/raw");
}

TEST(MQTTProtocol, GetTopicJSON_WithDevice) {
    char topic[MQTTProtocol::kMaxTopicSize];
    EXPECT_TRUE(MQTTProtocol::GetTopic(0xABCDEF, "status", topic, sizeof(topic),
                                        MQTTProtocol::kModeS, false, "mydevice"));
    EXPECT_STREQ(topic, "mydevice/adsb/ABCDEF/status");
}

TEST(MQTTProtocol, GetTopicShort_NoDevice) {
    char topic[MQTTProtocol::kMaxTopicSize];
    EXPECT_TRUE(MQTTProtocol::GetTopic(0xABCDEF, "raw", topic, sizeof(topic),
                                        MQTTProtocol::kModeS, true, nullptr));
    EXPECT_STREQ(topic, "a/ABCDEF/r");
}

TEST(MQTTProtocol, GetTopicShort_UAT_WithDevice) {
    char topic[MQTTProtocol::kMaxTopicSize];
    EXPECT_TRUE(MQTTProtocol::GetTopic(0x123456, "status", topic, sizeof(topic),
                                        MQTTProtocol::kUAT, true, "dev1"));
    EXPECT_STREQ(topic, "dev1/u/123456/s");
}

TEST(MQTTProtocol, GetTopicShort_Position) {
    char topic[MQTTProtocol::kMaxTopicSize];
    EXPECT_TRUE(MQTTProtocol::GetTopic(0xABCDEF, "position", topic, sizeof(topic),
                                        MQTTProtocol::kModeS, true, nullptr));
    EXPECT_STREQ(topic, "a/ABCDEF/p");
}

TEST(MQTTProtocol, GetTopic_NullBuffer) {
    EXPECT_FALSE(MQTTProtocol::GetTopic(0xABCDEF, "raw", nullptr, 64));
}

TEST(MQTTProtocol, GetTopic_NullMsgType) {
    char topic[MQTTProtocol::kMaxTopicSize];
    EXPECT_FALSE(MQTTProtocol::GetTopic(0xABCDEF, nullptr, topic, sizeof(topic)));
}

TEST(MQTTProtocol, GetTopic_BufferTooSmall) {
    char topic[8];  // Too small for most topics
    EXPECT_FALSE(MQTTProtocol::GetTopic(0xABCDEF, "raw", topic, sizeof(topic)));
}

// ---- Telemetry Topic Tests ----

TEST(MQTTProtocol, GetTelemetryTopicJSON_NoDevice) {
    char topic[MQTTProtocol::kMaxTopicSize];
    EXPECT_TRUE(MQTTProtocol::GetTelemetryTopic(topic, sizeof(topic), "telemetry", false, nullptr));
    EXPECT_STREQ(topic, "system/telemetry");
}

TEST(MQTTProtocol, GetTelemetryTopicJSON_Position_WithDevice) {
    char topic[MQTTProtocol::kMaxTopicSize];
    EXPECT_TRUE(MQTTProtocol::GetTelemetryTopic(topic, sizeof(topic), "position", false, "mydev"));
    EXPECT_STREQ(topic, "mydev/system/position");
}

TEST(MQTTProtocol, GetTelemetryTopicShort_NoDevice) {
    char topic[MQTTProtocol::kMaxTopicSize];
    EXPECT_TRUE(MQTTProtocol::GetTelemetryTopic(topic, sizeof(topic), "telemetry", true, nullptr));
    EXPECT_STREQ(topic, "sys/t");
}

TEST(MQTTProtocol, GetTelemetryTopicShort_Position_WithDevice) {
    char topic[MQTTProtocol::kMaxTopicSize];
    EXPECT_TRUE(MQTTProtocol::GetTelemetryTopic(topic, sizeof(topic), "position", true, "dev1"));
    EXPECT_STREQ(topic, "dev1/sys/g");
}

TEST(MQTTProtocol, GetTelemetryTopic_NullBuffer) {
    EXPECT_FALSE(MQTTProtocol::GetTelemetryTopic(nullptr, 64, "telemetry"));
}

TEST(MQTTProtocol, GetTelemetryTopic_NullMsgType) {
    char topic[MQTTProtocol::kMaxTopicSize];
    EXPECT_FALSE(MQTTProtocol::GetTelemetryTopic(topic, sizeof(topic), nullptr));
}

// ---- Packet Formatting Tests (Mode S) ----

TEST(MQTTProtocol, FormatPacketJSON) {
    // Create a Mode S packet from a hex string (DF17 ADS-B)
    DecodedModeSPacket packet((char *)"8d495066587f469bb826d21ad767",
                              0, -42, 50, 0x1234567890AB << 2);

    ASSERT_TRUE(packet.is_valid);

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatPacket(packet, buffer, sizeof(buffer),
                                               MQTTProtocol::kFormatJSON,
                                               MQTTProtocol::kModeS);
    ASSERT_GT(len, 0);

    // Parse the JSON string
    char *json = (char *)buffer;
    json[len] = '\0';

    // Verify JSON structure contains expected fields
    EXPECT_NE(strstr(json, "\"icao\":\"495066\""), nullptr);
    EXPECT_NE(strstr(json, "\"band\":\"1090\""), nullptr);
    EXPECT_NE(strstr(json, "\"df\":17"), nullptr);  // DF17 = ADS-B
    EXPECT_NE(strstr(json, "\"rssi\":-42"), nullptr);
    EXPECT_NE(strstr(json, "\"hex\":\""), nullptr);
}

TEST(MQTTProtocol, FormatPacketJSON_UAT_Band) {
    DecodedModeSPacket packet((char *)"8d495066587f469bb826d21ad767",
                              0, -42, 50, 0);
    ASSERT_TRUE(packet.is_valid);

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatPacket(packet, buffer, sizeof(buffer),
                                               MQTTProtocol::kFormatJSON,
                                               MQTTProtocol::kUAT);
    ASSERT_GT(len, 0);

    char *json = (char *)buffer;
    json[len] = '\0';
    EXPECT_NE(strstr(json, "\"band\":\"UAT\""), nullptr);
}

TEST(MQTTProtocol, FormatPacketBinary) {
    DecodedModeSPacket packet((char *)"8d495066587f469bb826d21ad767",
                              0, -42, 50, 0);
    ASSERT_TRUE(packet.is_valid);

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatPacket(packet, buffer, sizeof(buffer),
                                               MQTTProtocol::kFormatBinary,
                                               MQTTProtocol::kModeS);
    ASSERT_GT(len, 0);

    // Binary format: [Type:1][Band+Reserved:1][Data:7-14]
    EXPECT_EQ(buffer[0], MQTTProtocol::kBinaryRaw);
    // DF17 is long format = 14 data bytes + 2 header = 16 total
    EXPECT_EQ(len, 16);
    // Band in upper 2 bits of byte 1
    EXPECT_EQ((buffer[1] >> 6) & 0x03, MQTTProtocol::kModeS);
}

TEST(MQTTProtocol, FormatPacketBinary_UAT_Band) {
    DecodedModeSPacket packet((char *)"8d495066587f469bb826d21ad767",
                              0, -42, 50, 0);
    ASSERT_TRUE(packet.is_valid);

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatPacket(packet, buffer, sizeof(buffer),
                                               MQTTProtocol::kFormatBinary,
                                               MQTTProtocol::kUAT);
    ASSERT_GT(len, 0);
    EXPECT_EQ((buffer[1] >> 6) & 0x03, MQTTProtocol::kUAT);
}

TEST(MQTTProtocol, FormatPacket_ShortSquitter) {
    // DF0 short squitter (56 bits = 7 bytes)
    DecodedModeSPacket packet((char *)"02e197aa6e876c", 0, -50, 50, 0);
    // Note: some squitter packets may not decode as valid depending on CRC
    // Just test that the format function handles them

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatPacket(packet, buffer, sizeof(buffer),
                                               MQTTProtocol::kFormatBinary);

    if (packet.is_valid) {
        // Short format = 7 data bytes + 2 header = 9 total
        EXPECT_EQ(len, 9);
    }
}

TEST(MQTTProtocol, FormatPacket_NullBuffer) {
    DecodedModeSPacket packet;
    uint16_t len = MQTTProtocol::FormatPacket(packet, nullptr, 512, MQTTProtocol::kFormatJSON);
    EXPECT_EQ(len, 0);
}

TEST(MQTTProtocol, FormatPacket_BufferTooSmall) {
    DecodedModeSPacket packet((char *)"8d495066587f469bb826d21ad767",
                              0, -42, 50, 0);
    uint8_t buffer[5];  // Way too small
    uint16_t len = MQTTProtocol::FormatPacket(packet, buffer, sizeof(buffer),
                                               MQTTProtocol::kFormatJSON);
    EXPECT_EQ(len, 0);
}

// ---- Aircraft Formatting Tests ----

TEST(MQTTProtocol, FormatAircraftJSON) {
    ModeSAircraft aircraft;
    aircraft.icao_address = 0xABCDEF;
    strncpy(aircraft.callsign, "UAL123", 8);
    aircraft.latitude_deg = 37.77493f;
    aircraft.longitude_deg = -122.41942f;
    aircraft.baro_altitude_ft = 35000;
    aircraft.direction_deg = 270.0f;
    aircraft.speed_kts = 450;
    aircraft.baro_vertical_rate_fpm = -1200;
    aircraft.squawk = 0x1200;
    aircraft.emitter_category_raw = 0xA3;  // Category A3
    aircraft.flags = (1 << ModeSAircraft::kBitFlagIsAirborne);

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatAircraft(aircraft, buffer, sizeof(buffer),
                                                 MQTTProtocol::kFormatJSON,
                                                 MQTTProtocol::kModeS);
    ASSERT_GT(len, 0);

    char *json = (char *)buffer;
    json[len] = '\0';

    EXPECT_NE(strstr(json, "\"icao\":\"ABCDEF\""), nullptr);
    EXPECT_NE(strstr(json, "\"band\":\"1090\""), nullptr);
    EXPECT_NE(strstr(json, "\"call\":\"UAL123\""), nullptr);
    EXPECT_NE(strstr(json, "\"alt\":35000"), nullptr);
    EXPECT_NE(strstr(json, "\"spd\":450"), nullptr);
    EXPECT_NE(strstr(json, "\"vr\":-1200"), nullptr);
    EXPECT_NE(strstr(json, "\"sqk\":\"1200\""), nullptr);
    // Airborne aircraft should have gnd:0
    EXPECT_NE(strstr(json, "\"gnd\":0"), nullptr);
}

TEST(MQTTProtocol, FormatAircraftJSON_OnGround) {
    ModeSAircraft aircraft;
    aircraft.icao_address = 0x123456;
    aircraft.flags = 0;  // Not airborne = on ground

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatAircraft(aircraft, buffer, sizeof(buffer),
                                                 MQTTProtocol::kFormatJSON);
    ASSERT_GT(len, 0);

    char *json = (char *)buffer;
    json[len] = '\0';

    // Not airborne = on ground = gnd:1
    EXPECT_NE(strstr(json, "\"gnd\":1"), nullptr);
}

TEST(MQTTProtocol, FormatAircraftBinary) {
    ModeSAircraft aircraft;
    aircraft.icao_address = 0xABCDEF;
    strncpy(aircraft.callsign, "DAL456", 8);
    aircraft.latitude_deg = 40.6413f;
    aircraft.longitude_deg = -73.7781f;
    aircraft.baro_altitude_ft = 10000;
    aircraft.direction_deg = 180.0f;
    aircraft.speed_kts = 250;
    aircraft.baro_vertical_rate_fpm = 1500;
    aircraft.squawk = 0x7700;
    aircraft.emitter_category_raw = 0x60;
    aircraft.last_message_signal_strength_dbm = -30;
    aircraft.last_message_timestamp_ms = 1000000;
    aircraft.flags = (1 << ModeSAircraft::kBitFlagIsAirborne) |
                     (1 << ModeSAircraft::kBitFlagAlert);

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatAircraft(aircraft, buffer, sizeof(buffer),
                                                 MQTTProtocol::kFormatBinary,
                                                 MQTTProtocol::kModeS);
    ASSERT_EQ(len, sizeof(MQTTProtocol::BinaryAircraft));

    MQTTProtocol::BinaryAircraft *msg = (MQTTProtocol::BinaryAircraft *)buffer;
    EXPECT_EQ(msg->type, MQTTProtocol::kBinaryAircraft);
    EXPECT_EQ(msg->protocol, MQTTProtocol::kModeS);
    EXPECT_EQ(msg->icao24, 0xABCDEFu);
    EXPECT_EQ(msg->altitude_25ft, 10000 / 25);
    EXPECT_EQ(msg->category, 0x60);
}

TEST(MQTTProtocol, FormatAircraft_NullBuffer) {
    ModeSAircraft aircraft;
    uint16_t len = MQTTProtocol::FormatAircraft(aircraft, nullptr, 512, MQTTProtocol::kFormatJSON);
    EXPECT_EQ(len, 0);
}

// ---- Telemetry Formatting Tests ----

TEST(MQTTProtocol, FormatTelemetryJSON) {
    MQTTProtocol::TelemetryData telemetry = {};
    telemetry.uptime_sec = 3600;
    telemetry.messages_received = 42;
    telemetry.messages_sent = 100;
    telemetry.cpu_temp_c = 45;
    telemetry.memory_free_kb = 128;
    telemetry.rssi_noise_floor_dbm = -95;
    telemetry.receiver_1090_enabled = 1;
    telemetry.receiver_subg_enabled = 1;
    telemetry.wifi_connected = 1;
    telemetry.mqtt_connected = 1;
    telemetry.fw_major = 2;
    telemetry.fw_minor = 3;
    telemetry.fw_patch = 1;

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatTelemetry(telemetry, buffer, sizeof(buffer),
                                                  MQTTProtocol::kFormatJSON);
    ASSERT_GT(len, 0);

    char *json = (char *)buffer;
    json[len] = '\0';

    EXPECT_NE(strstr(json, "\"uptime\":3600"), nullptr);
    EXPECT_NE(strstr(json, "\"msgs_adsb_ps\":42"), nullptr);
    EXPECT_NE(strstr(json, "\"esp_temp\":45"), nullptr);
    EXPECT_NE(strstr(json, "\"noise_floor\":-95"), nullptr);
    EXPECT_NE(strstr(json, "\"fw_ver\":\"2.3.1\""), nullptr);
}

TEST(MQTTProtocol, FormatTelemetryJSON_WithMPS) {
    MQTTProtocol::TelemetryData telemetry = {};
    telemetry.uptime_sec = 100;
    telemetry.mps_total = 500;
    telemetry.mps_feed_count = 3;
    telemetry.mps_feeds[0] = 200;
    telemetry.mps_feeds[1] = 150;
    telemetry.mps_feeds[2] = 150;

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatTelemetry(telemetry, buffer, sizeof(buffer),
                                                  MQTTProtocol::kFormatJSON);
    ASSERT_GT(len, 0);

    char *json = (char *)buffer;
    json[len] = '\0';

    EXPECT_NE(strstr(json, "\"mps_total\":500"), nullptr);
    EXPECT_NE(strstr(json, "\"mps\":[200,150,150]"), nullptr);
}

TEST(MQTTProtocol, FormatTelemetryBinary) {
    MQTTProtocol::TelemetryData telemetry = {};
    telemetry.uptime_sec = 7200;  // 120 minutes
    telemetry.messages_received = 1000;
    telemetry.messages_sent = 500;
    telemetry.cpu_temp_c = 55;
    telemetry.memory_free_kb = 2048;  // 2 MB
    telemetry.rssi_noise_floor_dbm = -90;
    telemetry.receiver_1090_enabled = 1;
    telemetry.receiver_subg_enabled = 0;
    telemetry.wifi_connected = 1;
    telemetry.mqtt_connected = 1;

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatTelemetry(telemetry, buffer, sizeof(buffer),
                                                  MQTTProtocol::kFormatBinary);
    ASSERT_EQ(len, sizeof(MQTTProtocol::BinaryTelemetry));

    MQTTProtocol::BinaryTelemetry *msg = (MQTTProtocol::BinaryTelemetry *)buffer;
    EXPECT_EQ(msg->type, MQTTProtocol::kBinaryTelemetry);
    EXPECT_EQ(msg->uptime_min, 120u);  // 7200 sec / 60 = 120 min
    EXPECT_EQ(msg->msgs_rx_count, 1000);
    EXPECT_EQ(msg->msgs_tx_count, 500);
    EXPECT_EQ(msg->cpu_temp_c, 55);
    EXPECT_EQ(msg->noise_floor_dbm, -90);
    // Status bits: 1090=1, 978=0, wifi=1, mqtt=1 -> 0b00001101 = 0x0D
    EXPECT_EQ(msg->status, 0x0D);
}

TEST(MQTTProtocol, FormatTelemetry_NullBuffer) {
    MQTTProtocol::TelemetryData telemetry = {};
    uint16_t len = MQTTProtocol::FormatTelemetry(telemetry, nullptr, 512, MQTTProtocol::kFormatJSON);
    EXPECT_EQ(len, 0);
}

// ---- GNSS Formatting Tests ----

TEST(MQTTProtocol, FormatGNSSJSON) {
    MQTTProtocol::GNSSData gnss = {};
    gnss.latitude_deg = 37.774929;
    gnss.longitude_deg = -122.419418;
    gnss.altitude_m = 30.5f;
    gnss.fix_status = 2;  // 3D fix
    gnss.num_satellites = 12;
    gnss.hdop = 1.2f;
    gnss.timestamp_s = 1700000000;

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatGNSS(gnss, buffer, sizeof(buffer),
                                            MQTTProtocol::kFormatJSON);
    ASSERT_GT(len, 0);

    char *json = (char *)buffer;
    json[len] = '\0';

    EXPECT_NE(strstr(json, "\"fix\":\"3D\""), nullptr);
    EXPECT_NE(strstr(json, "\"sats\":12"), nullptr);
    EXPECT_NE(strstr(json, "\"lat_deg\":37."), nullptr);
    EXPECT_NE(strstr(json, "\"lon_deg\":-122."), nullptr);
}

TEST(MQTTProtocol, FormatGNSSJSON_NoFix) {
    MQTTProtocol::GNSSData gnss = {};
    gnss.fix_status = 0;

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatGNSS(gnss, buffer, sizeof(buffer),
                                            MQTTProtocol::kFormatJSON);
    ASSERT_GT(len, 0);

    char *json = (char *)buffer;
    json[len] = '\0';
    EXPECT_NE(strstr(json, "\"fix\":\"None\""), nullptr);
}

TEST(MQTTProtocol, FormatGNSSJSON_2DFix) {
    MQTTProtocol::GNSSData gnss = {};
    gnss.fix_status = 1;

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatGNSS(gnss, buffer, sizeof(buffer),
                                            MQTTProtocol::kFormatJSON);
    ASSERT_GT(len, 0);

    char *json = (char *)buffer;
    json[len] = '\0';
    EXPECT_NE(strstr(json, "\"fix\":\"2D\""), nullptr);
}

TEST(MQTTProtocol, FormatGNSSBinary) {
    MQTTProtocol::GNSSData gnss = {};
    gnss.latitude_deg = 37.77493;
    gnss.longitude_deg = -122.41942;
    gnss.altitude_m = 100.0f;
    gnss.fix_status = 2;
    gnss.num_satellites = 10;
    gnss.hdop = 1.5f;
    gnss.timestamp_s = 600;  // 10 minutes

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatGNSS(gnss, buffer, sizeof(buffer),
                                            MQTTProtocol::kFormatBinary);
    ASSERT_EQ(len, sizeof(MQTTProtocol::BinaryGNSS));

    MQTTProtocol::BinaryGNSS *msg = (MQTTProtocol::BinaryGNSS *)buffer;
    EXPECT_EQ(msg->type, MQTTProtocol::kBinaryGNSS);
    EXPECT_EQ(msg->altitude_m, 100);
    EXPECT_EQ(msg->fix, 2);
    EXPECT_EQ(msg->sats, 10);
    EXPECT_EQ(msg->hdop_e2, 150);  // 1.5 * 100
}

TEST(MQTTProtocol, FormatGNSS_NullBuffer) {
    MQTTProtocol::GNSSData gnss = {};
    uint16_t len = MQTTProtocol::FormatGNSS(gnss, nullptr, 512, MQTTProtocol::kFormatJSON);
    EXPECT_EQ(len, 0);
}

// ---- Category Code Tests (tested indirectly via FormatAircraftJSON) ----

TEST(MQTTProtocol, CategoryCode_InAircraftJSON) {
    ModeSAircraft aircraft;
    aircraft.icao_address = 0x123456;
    // CA=5 (maps to 'B'), TYPE=3 -> "B3"
    aircraft.emitter_category_raw = (5 << 5) | 3;

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatAircraft(aircraft, buffer, sizeof(buffer),
                                                 MQTTProtocol::kFormatJSON);
    ASSERT_GT(len, 0);

    char *json = (char *)buffer;
    json[len] = '\0';
    EXPECT_NE(strstr(json, "\"cat\":\"B3\""), nullptr);
}

// ---- Bandwidth Estimation Tests ----

TEST(MQTTProtocol, EstimateBandwidth_JSON) {
    uint32_t bw = MQTTProtocol::EstimateBandwidth(MQTTProtocol::kFormatJSON, 1000);
    EXPECT_EQ(bw, 250u * 1000u);  // ~250 bytes per JSON message
}

TEST(MQTTProtocol, EstimateBandwidth_Binary) {
    uint32_t bw = MQTTProtocol::EstimateBandwidth(MQTTProtocol::kFormatBinary, 1000);
    EXPECT_EQ(bw, 20u * 1000u);  // ~20 bytes per binary message
}

// ---- Format Parse/String Tests ----

TEST(MQTTProtocol, ParseFormat_JSON) {
    EXPECT_EQ(MQTTProtocol::ParseFormat("JSON"), MQTTProtocol::kFormatJSON);
    EXPECT_EQ(MQTTProtocol::ParseFormat("json"), MQTTProtocol::kFormatJSON);
}

TEST(MQTTProtocol, ParseFormat_Binary) {
    EXPECT_EQ(MQTTProtocol::ParseFormat("BINARY"), MQTTProtocol::kFormatBinary);
    EXPECT_EQ(MQTTProtocol::ParseFormat("binary"), MQTTProtocol::kFormatBinary);
}

TEST(MQTTProtocol, ParseFormat_Default) {
    EXPECT_EQ(MQTTProtocol::ParseFormat("unknown"), MQTTProtocol::kFormatJSON);
    EXPECT_EQ(MQTTProtocol::ParseFormat(nullptr), MQTTProtocol::kFormatJSON);
}

TEST(MQTTProtocol, FormatToString) {
    EXPECT_STREQ(MQTTProtocol::FormatToString(MQTTProtocol::kFormatJSON), "JSON");
    EXPECT_STREQ(MQTTProtocol::FormatToString(MQTTProtocol::kFormatBinary), "BINARY");
}

// ---- UAT Packet Formatting Tests ----

TEST(MQTTProtocol, FormatUATPacketJSON) {
    // Create a UAT packet with some raw data
    RawUATADSBPacket raw_uat;
    // Fill in minimal data for a short UAT ADS-B message
    raw_uat.buffer[0] = 0x00;  // Payload type (ADS-B with state vector, short)
    raw_uat.buffer[1] = 0xAB;  // ICAO address byte 1
    raw_uat.buffer[2] = 0xCD;  // ICAO address byte 2
    raw_uat.buffer[3] = 0xEF;  // ICAO address byte 3
    raw_uat.buffer_len_bytes = 18;  // Short UAT ADS-B
    raw_uat.sigs_dbm = -35;
    raw_uat.mlat_48mhz_64bit_counts = 48000000;  // 1 second

    DecodedUATADSBPacket packet(raw_uat);

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatUATPacket(packet, buffer, sizeof(buffer),
                                                  MQTTProtocol::kFormatJSON);

    if (len > 0) {
        char *json = (char *)buffer;
        json[len] = '\0';

        // UAT always uses "UAT" band
        EXPECT_NE(strstr(json, "\"band\":\"UAT\""), nullptr);
        EXPECT_NE(strstr(json, "\"rssi\":-35"), nullptr);
        EXPECT_NE(strstr(json, "\"hex\":\""), nullptr);
    }
}

TEST(MQTTProtocol, FormatUATPacketBinary) {
    RawUATADSBPacket raw_uat;
    raw_uat.buffer[0] = 0x00;
    raw_uat.buffer[1] = 0xAB;
    raw_uat.buffer[2] = 0xCD;
    raw_uat.buffer[3] = 0xEF;
    raw_uat.buffer_len_bytes = 18;
    raw_uat.sigs_dbm = -35;

    DecodedUATADSBPacket packet(raw_uat);

    uint8_t buffer[MQTTProtocol::kMaxMessageSize];
    uint16_t len = MQTTProtocol::FormatUATPacket(packet, buffer, sizeof(buffer),
                                                  MQTTProtocol::kFormatBinary);

    if (len > 0) {
        EXPECT_EQ(buffer[0], MQTTProtocol::kBinaryRaw);
        // Band in upper 2 bits of byte 1 should be BAND_978_MHZ (1)
        EXPECT_EQ((buffer[1] >> 6) & 0x03, MQTTProtocol::kUAT);
        // Data length = raw buffer + 2 byte header
        EXPECT_EQ(len, 18 + 2);
    }
}

TEST(MQTTProtocol, FormatUATPacket_NullBuffer) {
    DecodedUATADSBPacket packet;
    uint16_t len = MQTTProtocol::FormatUATPacket(packet, nullptr, 512, MQTTProtocol::kFormatJSON);
    EXPECT_EQ(len, 0);
}

