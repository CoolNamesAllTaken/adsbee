#ifndef CSBEE_UTILS_HH_
#define CSBEE_UTILS_HH_

#include "aircraft_dictionary.hh"
#include "stdio.h"

const uint16_t kCSBeeMessageStrMaxLen = 200;

inline uint16_t WriteCSBeeAircraftMessageStr(char message_buf[], const Aircraft &aircraft) {
    // #A:ICAO,FLAGS,CALL,SQ,LAT,LON,ALT_BARO,TRACK,VELH,VELV,SIGS,SIGQ,FPS,NICNAC,ALT_GEO,ECAT,CRC\r\n
    uint16_t num_chars =
        sprintf(message_buf, "#A:%000000X,%d,%s,%04o,%.5f,%.5f,%d,%.0f,%.0f,%d", aircraft.icao_address, aircraft.flags,
                aircraft.callsign, aircraft.squawk, aircraft.latitude_deg, aircraft.longitude_deg,
                aircraft.baro_altitude_ft, aircraft.heading_deg, aircraft.velocity_kts, aircraft.vertical_rate_fpm);
    if (num_chars < 0) return num_chars;
    // CALL
    // for (char c : aircraft.callsign) {
    //     comms_manager.iface_putc(iface, c);
    // }
    // // ,SQ,LAT,LON,ALT_BARO,TRACK,VELH,VELV,
    // comms_manager.iface_printf(iface, ",%d,%00.5f,%00.5f", aircraft.squawk, aircraft.latitude_deg,
    //                            aircraft.longitude_deg, aircraft.baro_altitude_ft);
}

#endif /* CSBEE_UTILS_HH_ */