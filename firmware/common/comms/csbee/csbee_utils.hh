#ifndef CSBEE_UTILS_HH_
#define CSBEE_UTILS_HH_

#include "aircraft_dictionary.hh"
#include "macros.hh"
#include "stdio.h"

const uint16_t kCSBeeMessageStrMaxLen = 200;
const uint16_t kCRCMaxNumChars = 4;  // 16 bits = 4 hex characters.
const uint16_t kEOLNumChars = 2;

/**
 * Dumps an Aircraft object into a string buffer in CSBee format. String buffer must be of length
 * kCSBeeMessageStrMaxLen.
 * @param[out] message_buf Character array to write into.
 * @param[in] aircraft Aircraft object to dump the contents of.
 * @retval Number of characters written to the string buffer, or a negative value if something went wrong.
 */
inline int16_t WriteCSBeeAircraftMessageStr(char message_buf[], const ModeSAircraft &aircraft) {
    // #A:ICAO,FLAGS,CALL,SQ,LAT,LON,ALT_BARO,TRACK,VELH,VELV,SIGS,SIGQ,FPS,NICNAC,ALT_GEO,ECAT,CRC\r\n

    // Build up SYSINFO bitfield.
    // Convert aircraft length and width to maximum dimension.
    uint32_t sysinfo = MAX(aircraft.length_m, aircraft.width_m) << 22;  // MDIM bitfield.
    // Convert GNSS antenna offset value to CSBee formatted bitfield.
    if (aircraft.gnss_antenna_offset_right_of_roll_axis_m != INT8_MAX) {
        sysinfo |= (((aircraft.gnss_antenna_offset_right_of_roll_axis_m > 0) & 0b1) << 21);         // GAOR bitfield.
        sysinfo |= (((ABS(aircraft.gnss_antenna_offset_right_of_roll_axis_m) >> 1) & 0b11) << 19);  // GAOD bitfield.
        sysinfo |= (0b1 << 18);                                                                     // GAOK bitfield.
    }
    sysinfo |= ((aircraft.system_design_assurance & 0b11) << 16);                 // SDA bitfield.
    sysinfo |= ((aircraft.source_integrity_level & 0b11) << 14);                  // SIL bitfield.
    sysinfo |= ((aircraft.geometric_vertical_accuracy & 0b11) << 12);             // GVA bitfield
    sysinfo |= ((aircraft.navigation_accuracy_category_position & 0b1111) << 8);  // NAC_p bitfield.
    sysinfo |= ((aircraft.navigation_accuracy_category_velocity & 0b111) << 5);   // NAC_v bitfield.
    sysinfo |= ((aircraft.navigation_integrity_category_baro & 0b1) << 4);        // NIC_baro bitfield.
    sysinfo |= ((aircraft.navigation_integrity_category & 0b1111));               // NIC bitfield.

    int16_t num_chars =  // Print everything except CRC into string buffer.
        snprintf(message_buf, kCSBeeMessageStrMaxLen - kCRCMaxNumChars - 1,
                 "#A:%06X,"                                        // ICAO, e.g. 3C65AC
                 "%X,"                                             // FLAGS, e.g. 123F35648
                 "%s,"                                             // CALL, e.g. N61ZP
                 "%04o,"                                           // SQUAWK, e.g. 7232
                 "%d,"                                             // ECAT, e.g. 14
                 "%.5f,"                                           // LAT, e.g. 57.57634
                 "%.5f,"                                           // LON, e.g. 17.59554
                 "%d,"                                             // ALT_BARO, e.g. 5000
                 "%d,"                                             // ALT_GEO, e.g. 5000
                 "%.0f,"                                           // TRACK, e.g. 35
                 "%d,"                                             // VELH, e.g. 464
                 "%d,"                                             // VELV_BARO, e.g. -1344
                 "%d,"                                             // VELV_GNSS, e.g. -1344
                 "%d,"                                             // SIGS, e.g. -92
                 "%d,"                                             // SIGQ, e.g. 2
                 "%d,"                                             // FPSAC, e.g. 3
                 "%d,"                                             // FPSS, e.g. 5
                 "%X,",                                            // SYSINFO, e.g. 31BE89F2
                 aircraft.icao_address,                            // ICAO
                 aircraft.flags,                                   // FLAGS
                 aircraft.callsign,                                // CALL
                 aircraft.squawk,                                  // SQUAWK
                 aircraft.category,                                // ECAT
                 aircraft.latitude_deg,                            // LAT
                 aircraft.longitude_deg,                           // LON
                 aircraft.baro_altitude_ft,                        // ALT_BARO
                 aircraft.gnss_altitude_ft,                        // ALT_GEO
                 aircraft.direction_deg,                           // TRACK
                 aircraft.speed_kts,                               // VELH
                 aircraft.baro_vertical_rate_fpm,                  // VELV_BARO
                 aircraft.gnss_vertical_rate_fpm,                  // VELV_GNSS
                 aircraft.last_message_signal_strength_dbm,        // SIGS
                 aircraft.last_message_signal_quality_db,          // SIGQ
                 aircraft.metrics.valid_squitter_frames,           // SFPS
                 aircraft.metrics.valid_extended_squitter_frames,  // ESFPS
                 sysinfo                                           // SYSINFO
        );
    if (num_chars < 0) return num_chars;  // Check if snprintf call got busted.

    // Append a CRC.
    uint16_t crc = CalculateCRC16((uint8_t *)message_buf, num_chars);
    uint16_t crc_num_chars = snprintf(message_buf + num_chars, kCRCMaxNumChars + kEOLNumChars + 1, "%X\r\n",
                                      crc);  // Add CRC to the message buffer.

    return num_chars + crc_num_chars;
}

inline int16_t WriteCSBeeStatisticsMessageStr(char message_buf[], uint16_t dps, uint16_t raw_sfps, uint16_t sfps,
                                              uint16_t raw_esfps, uint16_t esfps, uint16_t num_aircraft, uint32_t tscal,
                                              uint32_t uptime) {
    int16_t num_chars =  // Print everything except for CRC into string buffer.
        snprintf(message_buf, kCSBeeMessageStrMaxLen - kCRCMaxNumChars - 1,
                 "#S:%d,"  // DPS, e.g. 106
                 "%d,"     // RAW_SFPS e.g. 30
                 "%d,"     // SFPS, e.g. 20
                 "%d,"     // RAW_ESFPS e.g. 15
                 "%d,"     // ESFPS, e.g. 13
                 "%d,"     // NUM_AIRCRAFT, e.g. 13
                 "%d,"     // TSCAL, e.g. 13999415
                 "%d,",    // UPTIME, e.g. 134
                 dps, raw_sfps, sfps, raw_esfps, esfps, num_aircraft, tscal, uptime);
    if (num_chars < 0) return num_chars;  // Check if snprintf call got busted.

    // Append a CRC.
    uint16_t crc = CalculateCRC16((uint8_t *)message_buf, num_chars);
    uint16_t crc_num_chars = snprintf(message_buf + num_chars, kCRCMaxNumChars + kEOLNumChars + 1, "%X\r\n",
                                      crc);  // Add CRC to the message buffer.

    return num_chars + crc_num_chars;
}

#endif /* CSBEE_UTILS_HH_ */