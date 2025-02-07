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

// Begin modified by John McNelly 2025-02-07
#include <cstdint>
#include <cstring>

#include "protocol.h"

#ifndef MAVLINK_MESSAGE_LENGTHS
#define MAVLINK_MESSAGE_LENGTHS \
    {                           \
    }
#endif

#include "mavlink_msg_adsb_vehicle.h"
#include "mavlink_msg_heartbeat.h"
#include "mavlink_msg_message_interval.h"
#include "mavlink_msg_request_data_stream.h"

// End modified by John McNelly 2025-02-07
#endif /*MAVLINK_H*/
