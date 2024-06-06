/** @file
 *  @brief MAVLink comm protocol built from minimal.xml
 *  @see http://mavlink.org
 */
#ifndef MAVLINK_H
#define MAVLINK_H

#define MAVLINK_PRIMARY_XML_HASH -4486119638139692020

#ifndef MAVLINK_STX
#define MAVLINK_STX 253
#endif

#ifndef MAVLINK_ENDIAN
#define MAVLINK_ENDIAN MAVLINK_LITTLE_ENDIAN
#endif

#ifndef MAVLINK_ALIGNED_FIELDS
#define MAVLINK_ALIGNED_FIELDS 1
#endif

#ifndef MAVLINK_CRC_EXTRA
#define MAVLINK_CRC_EXTRA 1
#endif

#ifndef MAVLINK_COMMAND_24BIT
#define MAVLINK_COMMAND_24BIT 1
#endif

#include "version.h"

// Begin modified by John McNelly 2024-06-06
// #include "minimal.h"
#ifndef MAVLINK_MESSAGE_LENGTHS
#define MAVLINK_MESSAGE_LENGTHS \
    {}
#endif

#ifndef MAVLINK_MESSAGE_CRCS
#define MAVLINK_MESSAGE_CRCS                                  \
    {                                                         \
        {0, 50, 9, 9, 0, 0, 0}, { 300, 217, 22, 22, 0, 0, 0 } \
    }
#endif
#include "mavlink_msg_adsb_vehicle.h"

// End modified by John McNelly 2024-06-06
#endif /*MAVLINK_H*/
