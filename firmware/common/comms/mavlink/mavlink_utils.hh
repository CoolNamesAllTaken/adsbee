#pragma once

#include "aircraft_dictionary.hh"
#include "mavlink.h"
#include "stdint.h"

uint8_t AircraftCategoryToMAVLINKEmitterType(Aircraft::Category category);

mavlink_adsb_vehicle_t AircraftToMAVLINKADSBVehicleMessage(const Aircraft &aircraft);