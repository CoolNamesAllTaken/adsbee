#include "adsbee.hh"
#include "aircraft_dictionary.hh"
#include "hardware_unit_tests.hh"
#include "mode_s_packet.hh"

uint64_t TimeDictionaryPacketIngestUs() {
    DecodedModeSPacket odd_packet = DecodedModeSPacket((char *)"8D48C22D60AB00DEABC5DB78FCD6");  // odd
    odd_packet.GetRawPtr()->mlat_48mhz_64bit_counts = 1'000 * 48'000;
    DecodedModeSPacket even_packet = DecodedModeSPacket((char *)"8D48C22D60AB0452BFAD19A695E0");  // even
    even_packet.GetRawPtr()->mlat_48mhz_64bit_counts = 2'000 * 48'000;
    uint32_t icao = odd_packet.GetICAOAddress();

    // Clear the dictionary for a fresh start.
    adsbee.aircraft_dictionary.RemoveAircraft(icao);

    // Ingest the odd packet to initialize the aircraft.
    adsbee.aircraft_dictionary.IngestDecodedModeSPacket(odd_packet);
    adsbee.aircraft_dictionary.IngestDecodedModeSPacket(even_packet);
    ModeSAircraft *aircraft = adsbee.aircraft_dictionary.GetAircraftPtr(icao);

    // Increment the timestamp of the odd packet and ingest it again. Time how long it takes the CPR filter to run.
    odd_packet.GetRawPtr()->mlat_48mhz_64bit_counts += 3'000 * 48'000;
    uint64_t start_timestamp_us = get_time_since_boot_us();
    adsbee.aircraft_dictionary.IngestDecodedModeSPacket(odd_packet);
    uint64_t end_timestamp_us = get_time_since_boot_us();

    uint64_t time_elapsed_us = end_timestamp_us - start_timestamp_us;

    printf("Aircraft dictionary took %llu us to ingest a packet with the CPR filter %s.\n", time_elapsed_us,
           (adsbee.aircraft_dictionary.CPRPositionFilterIsEnabled() ? "enabled" : "disabled"));

    return time_elapsed_us;
}

UTEST(Dictionary, TestCPRFilterTiming) {
    bool original_cpr_filter_setting = adsbee.aircraft_dictionary.CPRPositionFilterIsEnabled();
    adsbee.aircraft_dictionary.SetCPRPositionFilterEnabled(false);
    EXPECT_LE(TimeDictionaryPacketIngestUs(), 100);

    adsbee.aircraft_dictionary.SetCPRPositionFilterEnabled(true);
    EXPECT_LE(TimeDictionaryPacketIngestUs(), 100);

    adsbee.aircraft_dictionary.SetCPRPositionFilterEnabled(original_cpr_filter_setting);
}