#pragma once
#include <cstdint>

// Maximum number of aircraft simultaneously tracked by AircraftDictionary.
// Referenced by both aircraft_dictionary.hh and the comms reporting snapshot infrastructure.
static constexpr uint16_t kAircraftDictionaryMaxNumAircraft = 200;
