#pragma once

#include "aircraft_dictionary.hh"
#include "mavlink.h"
#include "stdint.h"

uint8_t AircraftCategoryToMAVLINKEmitterType(Aircraft1090::Category category);

mavlink_adsb_vehicle_t AircraftToMAVLINKADSBVehicleMessage(const Aircraft1090 &aircraft);