#pragma once

#include "aircraft_dictionary.hh"
#include "mavlink.h"
#include "stdint.h"

uint8_t AircraftCategoryToMAVLINKEmitterType(ADSBTypes::EmitterCategory emitter_category);

mavlink_adsb_vehicle_t AircraftToMAVLINKADSBVehicleMessage(const ModeSAircraft &aircraft);