/**
 * This file is intended to be included as a fragment within the public portion of the CommsManager class definition in
 * comms.hh, allowing reporting function definitions to be used across platforms.
 */

static constexpr uint32_t kRawReportingIntervalMs = 100;  // Report packets internally at 10Hz.
static constexpr uint32_t kMAVLINKReportingIntervalMs = 1000;
static constexpr uint32_t kCSBeeReportingIntervalMs = 1000;
static constexpr uint32_t kGDL90ReportingIntervalMs = 1000;

/**
 * Reporting interfaces are different on different platforms. This union allows passing either a SerialInterface enum
 * value or a feed index to the reporting functions, which will then interpret the value appropriately based on the
 * platform.
 */
typedef uint16_t ReportSink;

// Reporting Functions
bool UpdateReporting(const ReportSink *sinks, const SettingsManager::ReportingProtocol *sink_protocols,
                     uint16_t num_sinks, const CompositeArray::RawPackets *packets_to_report = nullptr);

/**
 * Sends out RAW formatted transponder data on the selected serial interface.
 * @param[in] sinks Array of ReportSinks to broadcast RAW messages on.
 * @param[in] num_sinks Number of ReportSinks in the sinks array.
 * @param[in] packets CompositeArray::RawPackets struct with counts and pointers to arrays of each kind of packet to
 * report.
 * @retval True if successful, false if something broke.
 */
bool ReportRaw(ReportSink *sinks, uint16_t num_sinks, const CompositeArray::RawPackets &packets);

/**
 * Sends out Mode S Beast formatted transponder data on the selected serial interface. Reports all transponder
 * packets in the provided packets_to_report array, which is used to allow printing arbitrary blocks of transponder
 * packets received via the CommsManager's built-in transponder_packet_reporting_queue_.
 * @param[in] sinks Array of ReportSinks to broadcast Mode S Beast messages on.
 * @param[in] num_sinks Number of ReportSinks in the sinks array.
 * @param[in] packets CompositeArray::RawPackets struct with counts and pointers to arrays of each kind of packet to
 * report.
 * @param[in] protocol Reporting protocol to use. Must be one of kBeast, kBeastNoUAT, or kBeastNoUATUplink.
 * @retval True if successful, false if something broke.
 */
bool ReportBeast(ReportSink *sinks, uint16_t num_sinks, const CompositeArray::RawPackets &packets,
                 SettingsManager::ReportingProtocol protocol = SettingsManager::kBeast);

/**
 * Sends out comma separated aircraft information for each aircraft in the aircraft dictionary.
 * @param[in] sinks Array of ReportSinks to broadcast aircraft information on.
 * @param[in] num_sinks Number of ReportSinks in the sinks array.
 * @retval True if successful, false if something broke.
 */
bool ReportCSBee(ReportSink *sinks, uint16_t num_sinks);

/**
 * Sends a series of MAVLINK ADSB_VEHICLE messages on the selected serial interface, one for each tracked aircraft
 * in the aircraft dictionary, plus a MAVLINK MESSAGE_INTERVAL message used as a delimiter at the end of the train
 * of ADSB_VEHICLE messages.
 *
 * @param[in] sinks Array of ReportSinks to broadcast MAVLINK messages on. Note that this gets cast to a
 * @param[in] num_sinks Number of ReportSinks in the sinks array.
 * MAVLINK channel as a bit of a dirty hack under the hood, then un-cast back into a SerialInterface in the UART send
 * function within MAVLINK. Shhhhhhh it's fine for now.
 * @param[in] mavlink_version MAVLINK protocol version to use (1 or 2).
 * @retval True if successful, false if something went sideways.
 */
bool ReportMAVLINK(ReportSink *sinks, uint16_t num_sinks, uint8_t mavlink_version = 2);

/**
 * Reports the contents of the aircraft dictionary using the Garmin GDL90 protocol.
 * @param[in] sinks Array of ReportSinks to broadcast GDL90 messages on.
 * @param[in] num_sinks Number of ReportSinks in the sinks array.
 * @retval True if successful, false if something broke.
 */
bool ReportGDL90(ReportSink *sinks, uint16_t num_sinks);