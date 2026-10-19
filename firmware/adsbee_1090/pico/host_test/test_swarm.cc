#include <cstring>
#include <string>
#include <vector>

#include "aircraft_dictionary.hh"
#include "swarm_reporter.hh"
#include "geo_utils.hh"
#include "gtest/gtest.h"
#include "hal.hh"
#include "range_map.hh"

namespace {

uint16_t DegToBam16(float deg) { return static_cast<uint16_t>(deg * (65536.0f / 360.0f)); }

// Standard base64 decoder for checking what the reporter sends.
std::vector<uint8_t> Base64Decode(const std::string& text) {
    static const std::string kAlphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    std::vector<uint8_t> out;
    uint32_t v = 0;
    int bits = 0;
    for (char c : text) {
        if (c == '=') break;
        v = (v << 6) | kAlphabet.find(c);
        bits += 6;
        if (bits >= 8) {
            bits -= 8;
            out.push_back((v >> bits) & 0xFF);
        }
    }
    return out;
}

// The string value of "key":"..." in a JSON text, or "" if absent.
std::string JsonString(const std::string& json, const std::string& key) {
    size_t pos = json.find("\"" + key + "\":\"");
    if (pos == std::string::npos) return "";
    pos += key.size() + 4;
    return json.substr(pos, json.find('"', pos) - pos);
}

// The number after "key": in a JSON text, or -1 if absent.
long JsonNumber(const std::string& json, const std::string& key) {
    size_t pos = json.find("\"" + key + "\":");
    if (pos == std::string::npos) return -1;
    return strtol(json.c_str() + pos + key.size() + 3, nullptr, 10);
}

class FakeSwarmPlatform : public SwarmPlatform {
   public:
    uint32_t now_ms = 0;
    bool online = true;
    bool answer = true;
    int status = 200;
    uint32_t retry_after_s = 0;
    std::string response = "{\"next_report_s\": 3600, \"firmware\": null}";
    std::vector<std::string> urls;
    std::vector<std::string> bodies;
    std::vector<std::string> tokens;
    std::string target = "(unset)";
    std::string target_channel;

    uint32_t NowMs() override { return now_ms; }
    uint32_t Random() override { return 0; }
    bool Online() override { return online; }
    bool GetIdentity(AutoUpdatePlatform::Identity& identity) override {
        snprintf(identity.unique_id, sizeof(identity.unique_id), "E6614C311B5B6F2A");
        snprintf(identity.mac_address, sizeof(identity.mac_address), "02:00:00:AB:CD:EF");
        memset(identity.ota_keys[0], 'a', 128);
        memset(identity.ota_keys[1], 'b', 128);
        return true;
    }
    bool Http(const AutoUpdatePlatform::HttpRequest& request, AutoUpdatePlatform::HttpResult& result,
              AutoUpdatePlatform::BodySink* sink) override {
        urls.push_back(request.path);
        bodies.push_back(request.body ? request.body : "");
        tokens.push_back(request.token ? request.token : "");
        if (!answer) return false;
        result.status = status;
        result.retry_after_s = retry_after_s;
        // In two pieces, like a body split across reads.
        size_t half = response.size() / 2;
        sink->OnBody(status, reinterpret_cast<const uint8_t*>(response.data()), half);
        sink->OnBody(status, reinterpret_cast<const uint8_t*>(response.data()) + half, response.size() - half);
        return true;
    }
    void SetFirmwareTarget(const char* tag, const char* channel) override {
        target = tag ? tag : "";
        target_channel = channel ? channel : "";
    }
};

SwarmReporter::DeviceState FixedPosition() {
    SwarmReporter::DeviceState state;
    state.auto_update = true;
    state.rx_position_valid = true;
    state.latitude_deg = 37.1f;
    state.longitude_deg = -122.1f;
    state.altitude_m = 30;
    state.rx_position_source = "fixed";
    state.range_valid = true;
    return state;
}

void AddSecond(SwarmRecorder& r, uint32_t modes, uint32_t es, uint32_t uat, uint32_t uplink, uint16_t aircraft) {
    r.AddFrames(modes, es, uat, uplink);
    r.NoteAircraftCount(aircraft);
}

const char kToken[] = "0123456789abcdef0123456789abcdef";

}  // namespace

TEST(SwarmRange, AltitudeBands) {
    struct {
        int32_t ft;
        uint8_t band;
    } cases[] = {{-500, 0},  {0, 0},      {999, 0},    {1000, 1},   {1999, 1},   {2000, 2},  {3999, 2},
                 {4000, 3},  {5999, 3},   {6000, 4},   {9999, 4},   {10000, 5},  {14999, 5}, {15000, 6},
                 {19999, 6}, {20000, 7},  {24999, 7},  {25000, 8},  {29999, 8},  {30000, 9}, {34999, 9},
                 {35000, 10}, {39999, 10}, {40000, 11}, {60000, 11}, {INT32_MAX, 11}};
    for (const auto& c : cases) EXPECT_EQ(RangeMap::AltitudeBand(c.ft), c.band) << c.ft << " ft";
}

TEST(SwarmRange, SectorsAndDistanceValues) {
    EXPECT_EQ(RangeMap::Sector(0), 0);
    EXPECT_EQ(RangeMap::Sector(DegToBam16(9.99f)), 0);
    EXPECT_EQ(RangeMap::Sector(DegToBam16(10.01f)), 1);
    EXPECT_EQ(RangeMap::Sector(DegToBam16(90.5f)), 9);
    EXPECT_EQ(RangeMap::Sector(DegToBam16(359.9f)), 35);
    EXPECT_EQ(RangeMap::Sector(UINT16_MAX), 35);
    for (uint32_t bam = 0; bam <= UINT16_MAX; bam += 7) {
        ASSERT_EQ(RangeMap::Sector(bam), static_cast<uint8_t>(bam * 360.0 / 65536.0 / 10.0)) << bam;
    }

    EXPECT_EQ(RangeMap::DistanceValue(0), 1);
    EXPECT_EQ(RangeMap::DistanceValue(1), 1);
    EXPECT_EQ(RangeMap::DistanceValue(2000), 1);
    EXPECT_EQ(RangeMap::DistanceValue(2001), 2);
    EXPECT_EQ(RangeMap::DistanceValue(509999), 255);
    EXPECT_EQ(RangeMap::DistanceValue(510000), 255);
    EXPECT_EQ(RangeMap::DistanceValue(UINT32_MAX), 255);
}

TEST(SwarmRange, RecordKeepsTheMaximumPerBin) {
    RangeMap map;
    map.Record(50000, DegToBam16(45.0f), 12000);   // band 5, sector 4: 25
    map.Record(30000, DegToBam16(45.0f), 12000);   // smaller: kept 25
    map.Record(70500, DegToBam16(44.0f), 14999);   // same bin: 36
    map.Record(1000, DegToBam16(355.0f), 41000);   // band 11, sector 35: 1
    EXPECT_EQ(map.bins[5 * 36 + 4], 36);
    EXPECT_EQ(map.bins[11 * 36 + 35], 1);
    int num_set = 0;
    for (uint8_t b : map.bins) num_set += b != 0;
    EXPECT_EQ(num_set, 2);
}

TEST(SwarmRange, EncodeBitmapIsLSBFirstInBinOrder) {
    RangeMap map;
    map.bins[0] = 7;
    map.bins[9] = 200;
    map.bins[431] = 3;
    uint8_t bitmap[RangeMap::kBitmapLenBytes];
    uint8_t values[RangeMap::kNumBins];
    ASSERT_EQ(map.Encode(bitmap, values), 3);
    EXPECT_EQ(sizeof(bitmap), 54u);
    EXPECT_EQ(bitmap[0], 0x01);
    EXPECT_EQ(bitmap[1], 0x02);  // Bin 9: byte 1, bit 1.
    EXPECT_EQ(bitmap[53], 0x80);
    for (int i = 2; i < 53; i++) EXPECT_EQ(bitmap[i], 0) << i;
    EXPECT_EQ(values[0], 7);
    EXPECT_EQ(values[1], 200);
    EXPECT_EQ(values[2], 3);
}

TEST(SwarmRange, Base64MatchesTheStandardAlphabetWithPadding) {
    char out[16];
    EXPECT_EQ(SwarmReporter::Base64Encode(reinterpret_cast<const uint8_t*>(""), 0, out), 0u);
    EXPECT_STREQ(out, "");
    SwarmReporter::Base64Encode(reinterpret_cast<const uint8_t*>("f"), 1, out);
    EXPECT_STREQ(out, "Zg==");
    SwarmReporter::Base64Encode(reinterpret_cast<const uint8_t*>("fo"), 2, out);
    EXPECT_STREQ(out, "Zm8=");
    SwarmReporter::Base64Encode(reinterpret_cast<const uint8_t*>("foobar"), 6, out);
    EXPECT_STREQ(out, "Zm9vYmFy");
    const uint8_t high[] = {0xFB, 0xFF, 0xBF};
    SwarmReporter::Base64Encode(high, 3, out);
    EXPECT_STREQ(out, "+/+/");
}

TEST(SwarmRecorder, UniqueAircraftEstimate) {
    SwarmRecorder recorder;
    EXPECT_EQ(recorder.UniqueAircraft(), 0);
    for (int repeat = 0; repeat < 3; repeat++) {
        for (uint32_t icao = 0xA00000; icao < 0xA00000 + 500; icao++) recorder.MarkAircraft(icao);
    }
    EXPECT_NEAR(recorder.UniqueAircraft(), 500, 25);
    SwarmRecorder later;
    for (uint32_t icao = 0xA00000 + 250; icao < 0xA00000 + 1500; icao++) later.MarkAircraft(icao);
    recorder.Merge(later);  // Union: 1500 different aircraft.
    EXPECT_NEAR(recorder.UniqueAircraft(), 1500, 75);
}

TEST(SwarmRecorder, MergeTakesMaximaAndSums) {
    SwarmRecorder a, b;
    AddSecond(a, 10, 20, 3, 4, 50);
    a.range.bins[7] = 10;
    AddSecond(b, 1, 2, 3, 4, 70);
    AddSecond(b, 1, 2, 3, 4, 60);
    b.range.bins[7] = 5;
    b.range.bins[8] = 9;
    a.Merge(b);
    EXPECT_EQ(a.stats.modes_valid, 12u);
    EXPECT_EQ(a.stats.es_valid, 24u);
    EXPECT_EQ(a.stats.uat_adsb, 9u);
    EXPECT_EQ(a.stats.uat_uplink, 12u);
    EXPECT_EQ(a.stats.aircraft_max, 70);
    EXPECT_EQ(a.range.bins[7], 10);
    EXPECT_EQ(a.range.bins[8], 9);
}

TEST(SwarmReporter, DefaultServerOnly) {
    EXPECT_TRUE(SwarmReporter::IsDefaultServer("https://adsbee.aero"));
    EXPECT_TRUE(SwarmReporter::IsDefaultServer("https://ADSBee.aero/"));
    EXPECT_TRUE(SwarmReporter::IsDefaultServer("https://adsbee.aero:443"));
    EXPECT_FALSE(SwarmReporter::IsDefaultServer("http://adsbee.aero"));
    EXPECT_FALSE(SwarmReporter::IsDefaultServer("https://adsbee.aero.example.com"));
    EXPECT_FALSE(SwarmReporter::IsDefaultServer("https://adsbee.aero:8443"));
    EXPECT_FALSE(SwarmReporter::IsDefaultServer("https://evil.example/adsbee.aero"));
    EXPECT_FALSE(SwarmReporter::IsDefaultServer("https://swarm.example.com"));
}

TEST(SwarmReporter, ReportBodyFollowsProtocolV1) {
    FakeSwarmPlatform platform;
    SwarmReporter reporter(platform, "0.9.1-rc9");
    SwarmRecorder live;
    AddSecond(live, 100, 200, 3, 4, 17);
    live.MarkAircraft(0xABCDEF);
    live.RecordPosition(50000, DegToBam16(45.0f), 12000, 1);
    platform.now_ms = 3700 * 1000;
    reporter.Restart(live, 100 * 1000);  // Period starts at uptime 100 s.
    AddSecond(live, 100, 200, 3, 4, 17);
    live.RecordPosition(50000, DegToBam16(45.0f), 12000, 1);
    reporter.TakePeriod(live, 3700 * 1000, FixedPosition());
    EXPECT_EQ(live.stats.modes_valid, 0u);  // The live period starts over.

    platform.now_ms = 3701 * 1000;
    reporter.Send("https://adsbee.aero/", kToken);
    ASSERT_EQ(platform.bodies.size(), 1u);
    EXPECT_EQ(platform.urls[0], "https://adsbee.aero/api/swarm/v1/report");
    EXPECT_EQ(platform.tokens[0], kToken);
    const std::string& body = platform.bodies[0];
    EXPECT_EQ(body.rfind("{\"v\":1,\"product\":\"adsbee_1090\",\"unique_id\":\"E6614C311B5B6F2A\"", 0), 0u) << body;
    EXPECT_NE(body.find("\"ota_keys\":[\"" + std::string(128, 'a') + "\",\"" + std::string(128, 'b') + "\"]"),
              std::string::npos);
    EXPECT_NE(body.find("\"versions\":{\"rp2040\":\"0.9.1-rc9\",\"esp32\":\"0.9.1-rc9\"}"), std::string::npos);
    EXPECT_NE(body.find("\"auto_update\":true"), std::string::npos);
    EXPECT_EQ(JsonNumber(body, "uptime_s"), 3701);
    EXPECT_EQ(JsonNumber(body, "seq"), 0);
    EXPECT_NE(body.find("\"period\":{\"start_uptime_s\":100,\"len_s\":3600}"), std::string::npos);
    EXPECT_NE(body.find("\"rx_position\":{\"lat\":37.10000,\"lon\":-122.10000,\"alt_m\":30,\"source\":\"fixed\"}"),
              std::string::npos);
    EXPECT_NE(body.find("\"stats\":{\"modes_valid\":100,\"es_valid\":200,\"uat_adsb\":3,\"uat_uplink\":4,"
                        "\"aircraft_max\":17,\"aircraft_unique\":0}"),
              std::string::npos);
    EXPECT_NE(body.find("\"range\":{\"sectors\":36,\"bands\":12,\"unit_m\":2000,"), std::string::npos);
    std::vector<uint8_t> bitmap = Base64Decode(JsonString(body, "changed"));
    std::vector<uint8_t> values = Base64Decode(JsonString(body, "max"));
    ASSERT_EQ(bitmap.size(), 54u);
    ASSERT_EQ(values.size(), 1u);
    const int bin = 5 * 36 + 4;
    EXPECT_EQ(bitmap[bin / 8], 1 << (bin % 8));
    EXPECT_EQ(values[0], 25);
    EXPECT_EQ(body.back(), '}');
    EXPECT_EQ(reporter.seq(), 1u);
    EXPECT_FALSE(reporter.has_pending());
}

TEST(SwarmReporter, NoOTAKeysToOtherServersAndNoPositionFromAircraft) {
    FakeSwarmPlatform platform;
    SwarmReporter reporter(platform, "0.9.1-rc9");
    SwarmRecorder live;
    live.RecordPosition(50000, 0, 0, 1);
    reporter.TakePeriod(live, 60000, FixedPosition());
    reporter.Send("http://192.168.1.10:8000", kToken);
    ASSERT_EQ(platform.bodies.size(), 1u);
    EXPECT_EQ(platform.urls[0], "http://192.168.1.10:8000/api/swarm/v1/report");
    EXPECT_EQ(platform.bodies[0].find("ota_keys"), std::string::npos);
    EXPECT_NE(platform.bodies[0].find("\"range\":{"), std::string::npos);

    // An aircraft-derived position (UsablePosition() false): no rx_position, no range, stats still go.
    reporter.TakePeriod(live, 120000, SwarmReporter::DeviceState());
    reporter.Send("http://192.168.1.10:8000", kToken);
    const std::string& body = platform.bodies[1];
    EXPECT_EQ(body.find("rx_position"), std::string::npos);
    EXPECT_EQ(body.find("\"range\""), std::string::npos);
    EXPECT_EQ(body.find("range_dropped"), std::string::npos);
    EXPECT_NE(body.find("\"stats\":{"), std::string::npos);
    EXPECT_NE(body.find(",\"range_withheld\":\"no_position\"}"), std::string::npos) << body;
}

TEST(SwarmReporter, FailedReportMergesWithSameSeqAndStart) {
    FakeSwarmPlatform platform;
    SwarmReporter reporter(platform, "0.9.1-rc9");
    SwarmRecorder live;
    reporter.Restart(live, 200 * 1000);
    AddSecond(live, 10, 20, 0, 0, 5);
    live.RecordPosition(10000, DegToBam16(5.0f), 500, 1);   // bin 0: 5
    live.MarkAircraft(1);
    reporter.TakePeriod(live, 3800 * 1000, FixedPosition());

    platform.answer = false;
    platform.now_ms = 3800 * 1000;
    uint32_t retry_ms = reporter.Send("https://adsbee.aero", kToken);
    EXPECT_EQ(retry_ms, 60 * 1000u);  // First retry after a minute.
    EXPECT_TRUE(reporter.has_pending());
    EXPECT_EQ(reporter.seq(), 0u);
    EXPECT_STREQ(reporter.status().result, "no answer");

    // The next period merges into the pending report.
    AddSecond(live, 1, 2, 0, 0, 9);
    live.RecordPosition(4000, DegToBam16(5.0f), 500, 1);    // Smaller: bin 0 stays 5.
    live.RecordPosition(30000, DegToBam16(15.0f), 500, 1);  // bin 1: 15
    live.MarkAircraft(2);
    reporter.TakePeriod(live, 3860 * 1000, FixedPosition());
    platform.status = 503;
    platform.answer = true;
    retry_ms = reporter.Send("https://adsbee.aero", kToken);
    EXPECT_EQ(retry_ms, 120 * 1000u);  // Doubles.
    EXPECT_STREQ(reporter.status().result, "server error");

    reporter.TakePeriod(live, 3980 * 1000, FixedPosition());
    platform.status = 200;
    reporter.Send("https://adsbee.aero", kToken);
    ASSERT_EQ(platform.bodies.size(), 3u);
    for (const std::string& body : platform.bodies) {
        EXPECT_EQ(JsonNumber(body, "seq"), 0) << body;
        EXPECT_EQ(JsonNumber(body, "start_uptime_s"), 200) << body;
    }
    EXPECT_EQ(JsonNumber(platform.bodies[0], "len_s"), 3600);
    EXPECT_EQ(JsonNumber(platform.bodies[1], "len_s"), 3660);
    EXPECT_EQ(JsonNumber(platform.bodies[2], "len_s"), 3780);
    const std::string& last = platform.bodies[2];
    EXPECT_EQ(JsonNumber(last, "modes_valid"), 11);  // Counts cover the whole widened period.
    EXPECT_EQ(JsonNumber(last, "es_valid"), 22);
    EXPECT_EQ(JsonNumber(last, "aircraft_max"), 9);
    EXPECT_EQ(JsonNumber(last, "aircraft_unique"), 2);
    std::vector<uint8_t> values = Base64Decode(JsonString(last, "max"));
    ASSERT_EQ(values.size(), 2u);
    EXPECT_EQ(values[0], 5);
    EXPECT_EQ(values[1], 15);

    // Only a 200 takes a new seq; the next period starts where the merged one ended.
    EXPECT_EQ(reporter.seq(), 1u);
    reporter.TakePeriod(live, 7580 * 1000, FixedPosition());
    reporter.Send("https://adsbee.aero", kToken);
    EXPECT_EQ(JsonNumber(platform.bodies[3], "seq"), 1);
    EXPECT_EQ(JsonNumber(platform.bodies[3], "start_uptime_s"), 3980);
    EXPECT_EQ(JsonNumber(platform.bodies[3], "modes_valid"), 0);
    EXPECT_NE(platform.bodies[3].find("\"changed\":\"AAAA"), std::string::npos);  // Empty map.
    EXPECT_NE(platform.bodies[3].find("\"max\":\"\""), std::string::npos);
}

TEST(SwarmReporter, RangeStaysOutIfAnyMergedPeriodLackedAFixedPosition) {
    FakeSwarmPlatform platform;
    platform.answer = false;
    SwarmReporter reporter(platform, "0.9.1-rc9");
    SwarmRecorder live;
    SwarmReporter::DeviceState no_fix = FixedPosition();
    no_fix.range_valid = false;
    reporter.TakePeriod(live, 3600 * 1000, no_fix);
    reporter.Send("https://adsbee.aero", kToken);
    reporter.TakePeriod(live, 3660 * 1000, FixedPosition());
    platform.answer = true;
    reporter.Send("https://adsbee.aero", kToken);
    EXPECT_EQ(platform.bodies[1].find("\"range\""), std::string::npos);
}

TEST(SwarmReporter, ResponseSetsPeriodAndFirmwareTarget) {
    FakeSwarmPlatform platform;
    SwarmReporter reporter(platform, "0.9.1-rc9");
    SwarmRecorder live;
    platform.response = "{\"next_report_s\": 60, \"firmware\": {\"tag\": \"0.9.2\", \"channel\": \"stable\"}}";
    reporter.TakePeriod(live, 1000, FixedPosition());
    EXPECT_EQ(reporter.Send("https://adsbee.aero", kToken), 0u + 60 * 1000 - 30 * 1000);  // Jitter at most half.
    EXPECT_EQ(platform.target, "0.9.2");
    EXPECT_EQ(platform.target_channel, "stable");

    // Out-of-range periods are clamped; firmware null clears the target.
    platform.response = "{\"next_report_s\": 5, \"firmware\": null}";
    reporter.TakePeriod(live, 2000, FixedPosition());
    EXPECT_EQ(reporter.Send("https://adsbee.aero", kToken), 30 * 1000u);
    EXPECT_EQ(platform.target, "");
    platform.response = "{\"next_report_s\": 999999}";
    reporter.TakePeriod(live, 3000, FixedPosition());
    EXPECT_EQ(reporter.Send("https://adsbee.aero", kToken), (86400u - 60) * 1000);
    EXPECT_EQ(platform.target, "");
}

TEST(SwarmReporter, ErrorAnswers) {
    FakeSwarmPlatform platform;
    SwarmReporter reporter(platform, "0.9.1-rc9");
    SwarmRecorder live;

    // 429: Retry-After when longer than the backoff.
    platform.status = 429;
    platform.retry_after_s = 600;
    reporter.TakePeriod(live, 1000, FixedPosition());
    EXPECT_EQ(reporter.Send("https://adsbee.aero", kToken), 600 * 1000u);
    EXPECT_TRUE(reporter.has_pending());

    // 401: the report waits a period, still pending.
    platform.status = 401;
    EXPECT_EQ(reporter.Send("https://adsbee.aero", kToken), (3600u - 60) * 1000);
    EXPECT_TRUE(reporter.has_pending());
    EXPECT_STREQ(reporter.status().result, "rejected");
    EXPECT_EQ(reporter.status().last_http_status, 401);

    // 400: dropped, new seq.
    platform.status = 400;
    reporter.Send("https://adsbee.aero", kToken);
    EXPECT_FALSE(reporter.has_pending());
    EXPECT_EQ(reporter.seq(), 1u);

    // 410: stop until the token changes.
    platform.status = 410;
    reporter.TakePeriod(live, 2000, FixedPosition());
    reporter.Send("https://adsbee.aero", kToken);
    EXPECT_TRUE(reporter.status().stopped);
    reporter.TakePeriod(live, 3000, FixedPosition());
    size_t num_requests = platform.bodies.size();
    reporter.Send("https://adsbee.aero", kToken);
    EXPECT_EQ(platform.bodies.size(), num_requests);
    reporter.ClearStop();
    platform.status = 200;
    reporter.TakePeriod(live, 4000, FixedPosition());
    reporter.Send("https://adsbee.aero", kToken);
    EXPECT_EQ(platform.bodies.size(), num_requests + 1);
    EXPECT_STREQ(reporter.status().result, "ok");
}

TEST(SwarmReporter, FirstReportTwoToFiveMinutesAfterBoot) {
    FakeSwarmPlatform platform;
    SwarmReporter reporter(platform, "0.9.1-rc9");
    EXPECT_EQ(reporter.FirstDelayMs(0), 120 * 1000u);  // Random() == 0.
    EXPECT_EQ(reporter.FirstDelayMs(100 * 1000), 20 * 1000u);
    EXPECT_EQ(reporter.FirstDelayMs(400 * 1000), 120 * 1000u);  // Turned on later: 2-5 min from now.
}

TEST(SwarmReporter, FullBodyFits) {
    FakeSwarmPlatform platform;
    SwarmReporter reporter(platform, "0.9.1-rc9");
    SwarmRecorder live;
    for (int i = 0; i < RangeMap::kNumBins; i++) live.range.bins[i] = 255;
    AddSecond(live, UINT32_MAX / 2, UINT32_MAX / 2, UINT32_MAX / 2, UINT32_MAX / 2, UINT16_MAX);
    reporter.TakePeriod(live, 4000000000u, FixedPosition());
    reporter.Send("https://adsbee.aero", kToken);
    ASSERT_EQ(platform.bodies.size(), 1u);
    EXPECT_GT(platform.bodies[0].size(), 1000u);
    EXPECT_LT(platform.bodies[0].size(), SwarmReporter::kBodyMaxLen);
    EXPECT_EQ(Base64Decode(JsonString(platform.bodies[0], "max")).size(), 432u);
}

// Positions reach the range map once an aircraft has two accepted decodes.
TEST(SwarmRecorder, DictionaryRecordsConfirmedPositions) {
    AircraftDictionary dictionary;
    SwarmRecorder recorder;
    dictionary.SetSwarmRecorder(&recorder);
    dictionary.SetReferencePosition(48.0f, 18.0f);
    auto ingest = [&](const char* hex) {
        DecodedModeSPacket packet = DecodedModeSPacket((char*)hex);
        inc_time_since_boot_ms(500);
        packet.raw.mlat_48mhz_64bit_counts = get_time_since_boot_ms() * 48'000;
        EXPECT_TRUE(dictionary.IngestDecodedModeSPacket(packet));
    };
    auto num_bins = [&]() {
        int n = 0;
        for (uint8_t b : recorder.range.bins) n += b != 0;
        return n;
    };
    // 48.3 N 18.2 E: one decode, not recorded yet.
    ingest("8DBEE001589B803335F17E3806C1");
    ingest("8DBEE001589B87A9D1D79C757A00");
    dictionary.Update(get_time_since_boot_ms());
    EXPECT_EQ(num_bins(), 0);
    EXPECT_EQ(recorder.stats.es_valid, 0u);  // Frame counts come from the RP2040, not the dictionary.
    EXPECT_EQ(recorder.stats.aircraft_max, 1);
    EXPECT_EQ(recorder.UniqueAircraft(), 1);

    // Moved to 48.4 N: confirmed, recorded on the next Update().
    for (int i = 0; i < 2; i++) {
        ingest("8DBEE001589B804445F17E39A3D0");
        ingest("8DBEE001589B87BA99D79C52EE84");
    }
    dictionary.Update(get_time_since_boot_ms());
    ModeSAircraft* aircraft =
        dictionary.GetAircraftPtr<ModeSAircraft>(Aircraft::ICAOToUID(0xBEE001, Aircraft::kAircraftTypeModeS), false);
    ASSERT_TRUE(aircraft);
    EXPECT_EQ(aircraft->num_position_decodes, 2);
    ASSERT_EQ(num_bins(), 1);
    uint8_t band = RangeMap::AltitudeBand(aircraft->baro_altitude_ft);
    EXPECT_EQ(recorder.range.bins[band * 36 + 1], 24);  // 46897 m at 18.41 deg.
    EXPECT_EQ(recorder.UniqueAircraft(), 1);

    // Without a recorder nothing is touched.
    dictionary.SetSwarmRecorder(nullptr);
    recorder.Clear();
    ingest("8DBEE001589B803335F17E3806C1");
    ingest("8DBEE001589B87A9D1D79C757A00");
    dictionary.Update(get_time_since_boot_ms());
    EXPECT_EQ(num_bins(), 0);
    EXPECT_EQ(recorder.stats.aircraft_max, 0);
}

TEST(SwarmRecorder, OnlyDirectPositionsCountForRange) {
    ModeSAircraft mode_s(0xA46E6A);
    const ModeSAircraft::AddressType direct[] = {ModeSAircraft::kAddressTypeADSBICAO,
                                                 ModeSAircraft::kAddressTypeADSBICAONonTransponder,
                                                 ModeSAircraft::kAddressTypeADSBOther};
    const ModeSAircraft::AddressType relayed[] = {ModeSAircraft::kAddressTypeADSRICAO, ModeSAircraft::kAddressTypeTISBICAO,
                                                  ModeSAircraft::kAddressTypeADSROther,
                                                  ModeSAircraft::kAddressTypeTISBTrackFile,
                                                  ModeSAircraft::kAddressTypeTISBOther};
    for (auto type : direct) {
        mode_s.position_address_type = type;
        EXPECT_TRUE(AircraftDictionary::IsDirectPosition(mode_s)) << type;
    }
    for (auto type : relayed) {
        mode_s.position_address_type = type;
        EXPECT_FALSE(AircraftDictionary::IsDirectPosition(mode_s)) << type;
    }
    for (int q = 0; q <= 6; q++) {
        UATAircraft uat(0xA00001 | (q << Aircraft::kAddressQualifierBitShift));
        EXPECT_EQ(AircraftDictionary::IsDirectPosition(uat), q == 0 || q == 1 || q == 4 || q == 5) << q;
    }
}

TEST(SwarmReporter, UsablePositionIsFixedOrGNSSAndReal) {
    typedef SettingsManager::RxPosition P;
    EXPECT_TRUE(SwarmReporter::UsablePosition(true, P::kPositionSourceFixed, 37.1f, -122.1f));
    EXPECT_TRUE(SwarmReporter::UsablePosition(true, P::kPositionSourceGNSS, -33.9f, 151.2f));
    EXPECT_TRUE(SwarmReporter::UsablePosition(true, P::kPositionSourceFixed, 0.0f, 10.0f));
    EXPECT_FALSE(SwarmReporter::UsablePosition(false, P::kPositionSourceGNSS, 37.1f, -122.1f));  // No fix.
    EXPECT_FALSE(SwarmReporter::UsablePosition(true, P::kPositionSourceLowestAircraft, 37.1f, -122.1f));
    EXPECT_FALSE(SwarmReporter::UsablePosition(true, P::kPositionSourceAircraftMatchingICAO, 37.1f, -122.1f));
    EXPECT_FALSE(SwarmReporter::UsablePosition(true, P::kPositionSourceNone, 37.1f, -122.1f));
    EXPECT_FALSE(SwarmReporter::UsablePosition(true, P::kPositionSourceFixed, 0.0f, 0.0f));
    EXPECT_FALSE(SwarmReporter::UsablePosition(true, P::kPositionSourceFixed, 91.0f, 0.0f));
    EXPECT_FALSE(SwarmReporter::UsablePosition(true, P::kPositionSourceFixed, 10.0f, -181.0f));
    EXPECT_FALSE(SwarmReporter::UsablePosition(true, P::kPositionSourceFixed, NAN, 1.0f));
}

namespace {

// Horizon limit in km for a receiver at rx_m and a band top at top_ft, as the protocol defines it.
double HorizonKm(double rx_m, double top_ft) {
    return 1.15 * 4.12 * (sqrt(rx_m > 0 ? rx_m : 0) + sqrt(top_ft * 0.3048)) + 20;
}

// Great circle distance in meters and initial bearing in 1/65536 turns.
void DistanceAndBearing(double lat1, double lon1, double lat2, double lon2, uint32_t& distance_m, uint16_t& bam) {
    const double r = M_PI / 180;
    double dlat = (lat2 - lat1) * r, dlon = (lon2 - lon1) * r;
    double a = sin(dlat / 2) * sin(dlat / 2) + cos(lat1 * r) * cos(lat2 * r) * sin(dlon / 2) * sin(dlon / 2);
    distance_m = static_cast<uint32_t>(6371000 * 2 * atan2(sqrt(a), sqrt(1 - a)));
    double y = sin(dlon) * cos(lat2 * r), x = cos(lat1 * r) * sin(lat2 * r) - sin(lat1 * r) * cos(lat2 * r) * cos(dlon);
    double deg = fmod(atan2(y, x) / r + 360, 360);
    bam = static_cast<uint16_t>(deg / 360 * 65536);
}

// One hour of traffic around a receiver: mostly en route above 20,000 ft, a third low near airports. Positions are
// within the radio horizon of the real receiver. Feeds the distances as seen from `rx`.
void FeedTraffic(SwarmRecorder& recorder, double rx_lat, double rx_lon) {
    const double true_lat = 37.0, true_lon = -122.0;
    uint32_t seed = 12345;
    auto rnd = [&]() { return (seed = seed * 1103515245u + 12345u) / 4294967296.0; };
    for (uint32_t aircraft = 0; aircraft < 300; aircraft++) {
        bool low = aircraft % 3 == 0;
        int32_t alt_ft = low ? 500 + static_cast<int32_t>(rnd() * 5500) : 20000 + static_cast<int32_t>(rnd() * 19000);
        double top_ft = SwarmRecorder::kBandTopFt[RangeMap::AltitudeBand(alt_ft)];
        double max_km = low ? 60 : 300;  // Traffic density, not the horizon.
        double range_km = rnd() * (max_km < HorizonKm(30, top_ft) - 20 ? max_km : HorizonKm(30, top_ft) - 20);
        double brg = rnd() * 2 * M_PI;
        double lat = true_lat + range_km / 111.2 * cos(brg);
        double lon = true_lon + range_km / (111.2 * cos(true_lat * M_PI / 180)) * sin(brg);
        for (int sample = 0; sample < 20; sample++) {
            uint32_t distance_m;
            uint16_t bam;
            DistanceAndBearing(rx_lat, rx_lon, lat, lon, distance_m, bam);
            recorder.RecordPosition(distance_m, bam, alt_ft, 0xA00000 + aircraft);
        }
    }
}

}  // namespace

TEST(SwarmRecorder, HorizonLimitPerBand) {
    for (int32_t rx_m : {-50, 0, 30, 100, 1000}) {
        SwarmRecorder recorder;
        recorder.SetReceiverAltitude(rx_m);
        for (uint8_t band = 0; band < RangeMap::kNumBands; band++) {
            uint32_t limit_m = static_cast<uint32_t>(HorizonKm(rx_m, SwarmRecorder::kBandTopFt[band]) * 1000);
            int32_t alt_ft = band == 0 ? 0 : SwarmRecorder::kBandTopFt[band - 1];  // Bottom of the band.
            recorder.Clear();
            recorder.RecordPosition(limit_m - 100, 0, alt_ft, 1);
            recorder.RecordPosition(limit_m + 100, 0, alt_ft, 2);
            EXPECT_EQ(recorder.guard.num_positions, 2u) << rx_m << " m, band " << int(band);
            EXPECT_EQ(recorder.guard.num_dropped, 1u) << rx_m << " m, band " << int(band);
            EXPECT_EQ(recorder.range.bins[band * 36], RangeMap::DistanceValue(limit_m - 100));
        }
    }
    // 30 m antenna, 0-1k ft band: 1.15 * 4.12 * (5.48 + 17.46) + 20 = 128.7 km.
    SwarmRecorder recorder;
    recorder.SetReceiverAltitude(30);
    recorder.RecordPosition(128000, 0, 500, 1);
    recorder.RecordPosition(129500, 0, 500, 2);
    EXPECT_EQ(recorder.guard.num_dropped, 1u);
}

// The horizon guard catches gross position errors. A position 100 km off still sees most traffic inside each band's
// horizon (129 km below 1,000 ft, 163 km below 2,000 ft, ...), so it is kept; 300 km off is withheld.
TEST(SwarmRecorder, GrossPositionErrorWithholdsTheMap) {
    SwarmRecorder right;
    right.SetReceiverAltitude(30);
    FeedTraffic(right, 37.0, -122.0);
    EXPECT_EQ(right.guard.num_positions, 6000u);
    EXPECT_EQ(right.guard.num_dropped, 0u);
    EXPECT_FALSE(right.RangeImplausible());

    SwarmRecorder off_100_km;  // 0.9 degrees north.
    off_100_km.SetReceiverAltitude(30);
    FeedTraffic(off_100_km, 37.9, -122.0);
    EXPECT_LT(off_100_km.guard.num_dropped * 10, off_100_km.guard.num_positions);
    EXPECT_FALSE(off_100_km.RangeImplausible());

    SwarmRecorder off_300_km;  // 2.7 degrees north.
    off_300_km.SetReceiverAltitude(30);
    FeedTraffic(off_300_km, 39.7, -122.0);
    EXPECT_GE(off_300_km.guard.num_dropped * 10, off_300_km.guard.num_positions) << off_300_km.guard.num_dropped;
    EXPECT_EQ(off_300_km.guard.num_dropped_aircraft, SwarmRecorder::kWithholdDroppedAircraft);
    EXPECT_TRUE(off_300_km.RangeImplausible());
}

TEST(SwarmRecorder, WithholdNeedsTenPercentFromFiveAircraft) {
    SwarmRecorder recorder;
    recorder.SetReceiverAltitude(0);
    auto feed = [&](int good, int bad, int bad_aircraft) {
        recorder.Clear();
        for (int i = 0; i < good; i++) recorder.RecordPosition(10000, 0, 30000, 100 + i % 7);
        for (int i = 0; i < bad; i++) recorder.RecordPosition(400000, 0, 500, 1 + i % bad_aircraft);
    };
    feed(90, 10, 5);  // 10 %, 5 aircraft.
    EXPECT_TRUE(recorder.RangeImplausible());
    feed(91, 9, 5);  // 9 %.
    EXPECT_FALSE(recorder.RangeImplausible());
    feed(10, 90, 4);  // One aircraft short.
    EXPECT_FALSE(recorder.RangeImplausible());
    feed(10, 0, 1);
    EXPECT_FALSE(recorder.RangeImplausible());
    feed(0, 0, 1);
    EXPECT_FALSE(recorder.RangeImplausible());

    // A merged retry sums the counts and joins the aircraft.
    SwarmRecorder a, b;
    a.SetReceiverAltitude(0);
    b.SetReceiverAltitude(0);
    for (int i = 0; i < 3; i++) a.RecordPosition(400000, 0, 500, 1 + i);
    for (int i = 0; i < 3; i++) b.RecordPosition(400000, 0, 500, 3 + i);  // Aircraft 3 in both.
    for (int i = 0; i < 20; i++) b.RecordPosition(1000, 0, 500, 9);
    a.Merge(b);
    EXPECT_EQ(a.guard.num_positions, 26u);
    EXPECT_EQ(a.guard.num_dropped, 6u);
    EXPECT_EQ(a.guard.num_dropped_aircraft, 5);
    EXPECT_TRUE(a.RangeImplausible());
}

TEST(SwarmReporter, WithheldMapSaysWhyAndCountsDrops) {
    FakeSwarmPlatform platform;
    SwarmReporter reporter(platform, "0.9.1-rc9");
    SwarmRecorder live;
    live.SetReceiverAltitude(30);
    for (int i = 0; i < 50; i++) live.RecordPosition(20000, 0, 30000, 100);
    for (int i = 0; i < 10; i++) live.RecordPosition(300000, 0, 500, 1 + i);
    reporter.TakePeriod(live, 60000, FixedPosition());
    reporter.Send("https://adsbee.aero", kToken);
    const std::string& body = platform.bodies[0];
    EXPECT_NE(body.find("\"rx_position\":{"), std::string::npos);
    EXPECT_NE(body.find(",\"range_withheld\":\"implausible\",\"range_dropped\":10}"), std::string::npos) << body;
    EXPECT_EQ(body.find("\"range\""), std::string::npos);

    // A clean period: the map, with its drop count.
    for (int i = 0; i < 50; i++) live.RecordPosition(20000, 0, 30000, 100);
    live.RecordPosition(300000, 0, 500, 1);
    reporter.TakePeriod(live, 120000, FixedPosition());
    reporter.Send("https://adsbee.aero", kToken);
    EXPECT_NE(platform.bodies[1].find(",\"range_dropped\":1,\"range\":{"), std::string::npos) << platform.bodies[1];
    EXPECT_EQ(platform.bodies[1].find("range_withheld"), std::string::npos);
}
