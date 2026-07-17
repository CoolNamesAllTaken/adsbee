#pragma once
#include <cstdint>

// Maximum number of aircraft simultaneously tracked by AircraftDictionary.
// Referenced by both aircraft_dictionary.hh and the comms reporting snapshot infrastructure.
// Override at compile time by defining AIRCRAFT_DICTIONARY_MAX_NUM_AIRCRAFT.
#ifndef AIRCRAFT_DICTIONARY_MAX_NUM_AIRCRAFT
#define AIRCRAFT_DICTIONARY_MAX_NUM_AIRCRAFT 200
#endif
static constexpr uint16_t kAircraftDictionaryMaxNumAircraft = AIRCRAFT_DICTIONARY_MAX_NUM_AIRCRAFT;

// When the dictionary is a downstream consumer of pre-validated packets (e.g., ESP32 receiving
// packets forwarded by the RP2040), trust the upstream validator for address-parity squitters
// even if the aircraft isn't in the local dictionary yet.
#ifdef ON_ESP32
#define AIRCRAFT_DICTIONARY_TRUST_FORWARDED_ADDRESS_PARITY
#endif
