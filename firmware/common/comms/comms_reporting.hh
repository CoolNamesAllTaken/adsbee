/**
 * This file is intended to be included as a fragment within the public portion of the CommsManager class definition in
 * comms.hh, allowing reporting function definitions to be used across platforms.
 */

// Reporting Functions
bool UpdateReporting();

/**
 * Reporting interfaces are different on different platforms. This union allows passing either a SerialInterface enum
 * value or a feed index to the reporting functions, which will then interpret the value appropriately based on the
 * platform.
 */
union ReportSink {
    SettingsManager::SerialInterface as_serial_interface;
    int16_t as_feed_index;
    uint16_t as_uint16_t;  // Used for easy casting to other types that are uint16_t or smaller.

    ReportSink(uint16_t val) : as_uint16_t(val) {}
    ReportSink(int16_t feed_index) : as_feed_index(feed_index) {}
    ReportSink(SettingsManager::SerialInterface serial_interface) : as_serial_interface(serial_interface) {}
};

/**
 * Sends out RAW formatted transponder data on the selected serial interface.
 * @param[in] sink SerialInterface or feed socket to broadcast RAW messages on.
 * @param[in] packets CompositeArray::RawPackets struct with counts and pointers to arrays of each kind of packet to
 * report.
 * @retval True if successful, false if something broke.
 */
bool ReportRaw(ReportSink sink, const CompositeArray::RawPackets &packets);

/**
 * Sends out Mode S Beast formatted transponder data on the selected serial interface. Reports all transponder
 * packets in the provided packets_to_report array, which is used to allow printing arbitrary blocks of transponder
 * packets received via the CommsManager's built-in transponder_packet_reporting_queue_.
 * @param[in] sink SerialInterface or feed socket to broadcast Mode S Beast messages on.
 * @param[in] packets CompositeArray::RawPackets struct with counts and pointers to arrays of each kind of packet to
 * report.
 */
bool ReportBeast(ReportSink sink, const CompositeArray::RawPackets &packets);

/**
 * Sends out comma separated aircraft information for each aircraft in the aircraft dictionary.
 * @param[in] sink SerialInterface or feed socket to broadcast aircraft information on.
 * @retval True if successful, false if something broke.
 */
bool ReportCSBee(ReportSink sink);

/**
 * Sends a series of MAVLINK ADSB_VEHICLE messages on the selected serial interface, one for each tracked aircraft
 * in the aircraft dictionary, plus a MAVLINK MESSAGE_INTERVAL message used as a delimiter at the end of the train
 * of ADSB_VEHICLE messages.
 * @param[in] sink SerialInterface or feed socket to broadcast MAVLINK messages on. Note that this gets cast to a
 * MAVLINK channel as a bit of a dirty hack under the hood, then un-cast back into a SerialInterface in the UART send
 * function within MAVLINK. Shhhhhhh it's fine for now.
 * @retval True if successful, false if something went sideways.
 */
bool ReportMAVLINK(ReportSink sink);

/**
 * Reports the contents of the aircraft dictionary using the Garmin GDL90 protocol.
 */
bool ReportGDL90(ReportSink sink);