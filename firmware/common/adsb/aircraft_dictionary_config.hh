#pragma once
#include <cstdint>

// Maximum number of aircraft simultaneously tracked by AircraftDictionary.
// Referenced by both aircraft_dictionary.hh and the comms reporting snapshot infrastructure.
// Override at compile time by defining AIRCRAFT_DICTIONARY_MAX_NUM_AIRCRAFT.
#ifndef AIRCRAFT_DICTIONARY_MAX_NUM_AIRCRAFT
#define AIRCRAFT_DICTIONARY_MAX_NUM_AIRCRAFT 200
#endif
static constexpr uint16_t kAircraftDictionaryMaxNumAircraft = AIRCRAFT_DICTIONARY_MAX_NUM_AIRCRAFT;
