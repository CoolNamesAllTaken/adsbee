#include "adsbee_server.hh"

#include "comms.hh"
#include "nvs_flash.h"
#include "settings.hh"
#include "spi_coprocessor.hh"
#include "task_priorities.hh"

// #define VERBOSE_DEBUG

// This will cause weird crashes if it's too small to support full size SPI transfers!
static const uint32_t kSPIRxTaskStackDepthBytes = 6 * 4096;
static const uint16_t kGDL90Port = 4000;

GDL90Reporter gdl90;

void esp_spi_receive_task(void *pvParameters) {
    adsbee_server.SPIReceiveTask();  // Only returns during DeInit.
    vTaskDelete(NULL);               // Delete this task.
}

bool ADSBeeServer::Init() {
    if (!pico.Init()) {
        CONSOLE_ERROR("ADSBeeServer::Init", "SPI Coprocessor initialization failed.");
        return false;
    }

    spi_receive_task_should_exit_ = false;
    xTaskCreatePinnedToCore(esp_spi_receive_task, "spi_receive_task", kSPIRxTaskStackDepthBytes, NULL,
                            kSPIReceiveTaskPriority, NULL, kSPIReceiveTaskCore);

    while (true) {
        if (!pico.Read(ObjectDictionary::kAddrSettingsData, settings_manager.settings)) {
            CONSOLE_ERROR("ADSBeeServer::Init", "Failed to read settings from Pico on startup.");
            vTaskDelay(500 / portTICK_PERIOD_MS);  // Delay for 0.5s before retry.
            continue;
        } else {
            settings_manager.Print();
            settings_manager.Apply();
            break;
        }
    }

    // Initialize Non Volatile Storage Flash, used by WiFi library.
    esp_err_t ret = nvs_flash_init();
    if (ret == ESP_ERR_NVS_NO_FREE_PAGES || ret == ESP_ERR_NVS_NEW_VERSION_FOUND) {
        ESP_ERROR_CHECK(nvs_flash_erase());
        ret = nvs_flash_init();
    }
    ESP_ERROR_CHECK(ret);

    if (!comms_manager.WiFiInit()) {
        CONSOLE_ERROR("ADSBeeServer::Init", "Failed to initialize WiFi.");
        return false;
    }

    return true;
}

bool ADSBeeServer::Update() {
    bool ret = true;
    // Do NOT call pico.Update() from here since that's already taken care of by the SPIReceiveTask.
    // Update the LED here so it has better time resolution than it would in the SPI task, which blocks frequently.
    pico.UpdateNetworkLED();

    uint32_t timestamp_ms = get_time_since_boot_ms();
    // Prune aircraft dictionary. Need to do this up front so that we don't end up with a negative timestamp delta
    // caused by packets being ingested more recently than the timestamp we take at the beginning of this function.
    if (timestamp_ms - last_aircraft_dictionary_update_timestamp_ms_ > kAircraftDictionaryUpdateIntervalMs) {
        uint32_t scratch;
        if (!pico.Read(ObjectDictionary::Address::kAddrScratch, scratch)) {
            CONSOLE_ERROR("ADSBeeServer::Update", "Read of Pico scratch failed.");
        }

        aircraft_dictionary.Update(timestamp_ms);
        last_aircraft_dictionary_update_timestamp_ms_ = timestamp_ms;
        CONSOLE_INFO("ADSBeeServer::Update", "\t %d clients, %d aircraft, %lu squitter, %lu extended squitter",
                     comms_manager.GetNumWiFiClients(), aircraft_dictionary.GetNumAircraft(),
                     aircraft_dictionary.stats.valid_squitter_frames,
                     aircraft_dictionary.stats.valid_extended_squitter_frames);
    }

    // Ingest new packets into the dictionary.
    RawTransponderPacket raw_packet;
    while (transponder_packet_queue.Pop(raw_packet)) {
        DecodedTransponderPacket decoded_packet = DecodedTransponderPacket(raw_packet);
#ifdef VERBOSE_DEBUG
        if (raw_packet.buffer_len_bits == DecodedTransponderPacket::kExtendedSquitterPacketLenBits) {
            CONSOLE_INFO("ADSBeeServer::Update", "New message: 0x%08lx|%08lx|%08lx|%04lx RSSI=%ddBm MLAT=%llu",
                         raw_packet.buffer[0], raw_packet.buffer[1], raw_packet.buffer[2],
                         (raw_packet.buffer[3]) >> (4 * kBitsPerNibble), raw_packet.sigs_dbm,
                         raw_packet.mlat_48mhz_64bit_counts);
        } else {
            CONSOLE_INFO("ADSBeeServer::Update", "New message: 0x%08lx|%06lx RSSI=%ddBm MLAT=%llu",
                         raw_packet.buffer[0], (raw_packet.buffer[1]) >> (2 * kBitsPerNibble), raw_packet.sigs_dbm,
                         raw_packet.mlat_48mhz_64bit_counts);
        }
        CONSOLE_INFO("ADSBeeServer::Update", "\tdf=%d icao_address=0x%06lx", decoded_packet.GetDownlinkFormat(),
                     decoded_packet.GetICAOAddress());
#endif

        if (aircraft_dictionary.IngestDecodedTransponderPacket(decoded_packet)) {
            // NOTE: Pushing to the reporting queue here means that we only will report validated packets!
            // comms_manager.transponder_packet_reporting_queue.Push(decoded_packet);
#ifdef VERBOSE_DEBUG
            CONSOLE_INFO("ADSBeeServer::Update", "\taircraft_dictionary: %d aircraft",
                         aircraft_dictionary.GetNumAircraft());
#endif
        }
    }

    // Broadcast aircraft locations to connected WiFi clients over GDL90.
    if (timestamp_ms - last_gdl90_report_timestamp_ms_ > kGDL90ReportingIntervalMs) {
        last_gdl90_report_timestamp_ms_ = timestamp_ms;
        if (!ReportGDL90()) {
            CONSOLE_ERROR("ADSBeeServer::Update", "Encountered error while reporting GDL90.");
            ret = false;
        }
    }
    return ret;
}

bool ADSBeeServer::HandleRawTransponderPacket(RawTransponderPacket &raw_packet) {
    bool ret = true;
    if (!transponder_packet_queue.Push(raw_packet)) {
        CONSOLE_ERROR("ADSBeeServer::HandleRawTransponderPacket",
                      "Push to transponder packet queue failed. May have overflowed?");
        ret = false;
    }

    if (!comms_manager.WiFiStationSendRawTransponderPacket(raw_packet)) {
        CONSOLE_ERROR("ADSBeeServer::HandleRawTransponderPacket",
                      "Encountered error while sending raw transponder packet to feeds from ESP32 as WiFi station.");
        ret = false;
    }
    return ret;
}

void ADSBeeServer::SPIReceiveTask() {
    ESP_LOGI("SPICoprocessor::SPIReceiveTask", "Started SPI receive task.");

    while (!spi_receive_task_should_exit_) {
        // Wait for a transaction to complete. Allow this task to block if no SPI transaction is received by using
        // max delay.
        pico.Update();
    }

    ESP_LOGI("esp_spi_receive_task", "Received exit signal, ending SPI receive task.");
}

bool ADSBeeServer::ReportGDL90() {
    CommsManager::NetworkMessage message;
    message.port = kGDL90Port;

    // Heartbeat Message
    message.len = gdl90.WriteGDL90HeartbeatMessage(message.data, get_time_since_boot_ms() / 1000,
                                                   aircraft_dictionary.stats.valid_extended_squitter_frames);
    comms_manager.WiFiAccessPointSendMessageToAllStations(message);

    // Ownship Report
    GDL90Reporter::GDL90TargetReportData ownship_data;
    // TODO: Actually fill out ownship data!
    // message.len = gdl90.WriteGDL90TargetReportMessage(message.data, ownship_data, true);
    comms_manager.WiFiAccessPointSendMessageToAllStations(message);

    // Traffic Reports
    uint16_t aircraft_index = 0;  // Just used for error reporting.
    for (auto &itr : aircraft_dictionary.dict) {
        const Aircraft &aircraft = itr.second;
        printf("\t%s: %.5f %.5f %ld\r\n", aircraft.callsign, aircraft.latitude_deg, aircraft.longitude_deg,
               aircraft.baro_altitude_ft);
        message.len = gdl90.WriteGDL90TargetReportMessage(message.data, aircraft, false);
        if (settings_manager.settings.wifi_ap_enabled &&
            !comms_manager.WiFiAccessPointSendMessageToAllStations(message)) {
            CONSOLE_ERROR("ADSBeeServer::ReportGDL90", "Failed to send info about aircraft %d to all clients.",
                          aircraft_index);
        }
        aircraft_index++;
    }
    return true;
}