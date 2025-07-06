#pragma once

#include "data_structures.hh" // For PFBQueue.
#include "settings.hh"
#include "transponder_packet.hh"

class CommsManager
{
public:
    static constexpr uint16_t kPrintfBufferMaxSize = 500;
    static constexpr uint32_t kRawReportingIntervalMs = 100; // Report packets internally at 10Hz.
    static constexpr uint32_t kMAVLINKReportingIntervalMs = 1000;
    static constexpr uint32_t kCSBeeReportingIntervalMs = 1000;
    static constexpr uint32_t kGDL90ReportingIntervalMs = 1000;

    static constexpr uint32_t kOTAWriteTimeoutMs = 5000; // ms until OTA write command exits if all bytes not received.

    struct CommsManagerConfig
    {
    };

    CommsManager(CommsManagerConfig config_in);

    /**
     * Initialize the CommsManager. Sets up UARTs and other necessary peripherals.
     * @retval True if initialization succeeded, false otherwise.
     */
    bool Init();

    /**
     * Update the CommsManager. Runs all the update subroutines required for normal operation.
     * @retval True if update succeeded, false otherwise.
     */
    bool Update();

    // Queue for storing transponder packets before they get reported.
    PFBQueue<Decoded1090Packet> transponder_packet_reporting_queue =
        PFBQueue<Decoded1090Packet>({.buf_len_num_elements = SettingsManager::Settings::kMaxNumTransponderPackets,
                                     .buffer = transponder_packet_reporting_queue_buffer_});

private:
    CommsManagerConfig config_;

    // Queue for holding new transponder packets before they get reported.
    Decoded1090Packet transponder_packet_reporting_queue_buffer_[SettingsManager::Settings::kMaxNumTransponderPackets];
};

extern CommsManager comms_manager;

#define CONSOLE_ERROR(tag, ...) \
    comms_manager.LogMessageToCoprocessor(SettingsManager::LogLevel::kErrors, tag, __VA_ARGS__);
#define CONSOLE_WARNING(tag, ...) \
    comms_manager.LogMessageToCoprocessor(SettingsManager::LogLevel::kWarnings, tag, __VA_ARGS__);
#define CONSOLE_INFO(tag, ...) \
    comms_manager.LogMessageToCoprocessor(SettingsManager::LogLevel::kInfo, tag, __VA_ARGS__);
// #define CONSOLE_PRINTF(...) printf(__VA_ARGS__);