#include "adsbee_server.hh"

#include "comms.hh"
#include "settings.hh"
#include "spi_coprocessor.hh"

static const uint32_t kSPIRxTaskStackDepthBytes = 4096;

void esp_spi_receive_task(void *pvParameters) {
    adsbee_server.SPIReceiveTask();  // Only returns during DeInit.
    vTaskDelete(NULL);               // Delete this task.
}

bool ADSBeeServer::Init() {
    if (!pico.Init()) return false;

    spi_receive_task_should_exit_ = false;
    xTaskCreate(esp_spi_receive_task, "spi_receive_task", kSPIRxTaskStackDepthBytes, NULL, 5, NULL);

    pico.Read(settings_manager.settings);

    return true;
}

bool ADSBeeServer::Update() {
    // Do NOT call pico.Update() from here since that's already taken care of by the SPIReceiveTask.
    // Run the LED task here so it has better time resolution than it would in the SPI task, which blocks frequently.
    pico.UpdateNetworkLED();
    return true;
}

bool ADSBeeServer::HandleRawTransponderPacket(RawTransponderPacket raw_packet) {
    switch (raw_packet.buffer_len_bits) {
        case DecodedTransponderPacket::kExtendedSquitterPacketLenBits:
            CONSOLE_INFO("ADSBeeServer::HandleRawTransponderpacket",
                         "Received Extended Squitter RawTransponderPacket.");
            // CONSOLE_INFO("ADSBeeServer::HandleRawTransponderPacket",
            //              "New message: 0x%08x|%08x|%08x|%04x RSSI=%ddBm MLAT=%lu", raw_packet.buffer[0],
            //              raw_packet.buffer[1], raw_packet.buffer[2], (raw_packet.buffer[3]) >> (4 * kBitsPerNibble),
            //              raw_packet.rssi_dbm, raw_packet.mlat_48mhz_64bit_counts);
            break;
        case DecodedTransponderPacket::kSquitterPacketLenBits:
            CONSOLE_INFO("ADSBeeServer::HandleRawTransponderpacket", "Received Squitter RawTransponderPacket.");
            // CONSOLE_INFO("ADSBee::Update", "New message: 0x%08x|%06x RSSI=%ddBm MLAT=%lu", raw_packet.buffer[0],
            //              (raw_packet.buffer[1]) >> (2 * kBitsPerNibble), raw_packet.rssi_dbm,
            //              raw_packet.mlat_48mhz_64bit_counts);
            break;
        default:
            CONSOLE_ERROR("ADSBeeServer::HandleRawTransponderpacket",
                          "Received transponder packet with invalid bit length %d.", raw_packet.buffer_len_bits);
            return false;
    }
    return true;
}

void ADSBeeServer::SPIReceiveTask() {
    ESP_LOGI("SPICoprocessor::SPIReceiveTask", "Started SPI receive task.");

    while (!spi_receive_task_should_exit_) {
        // Wait for a transaction to complete. Allow this task to block if no SPI transaction is received by using max
        // delay.
        pico.Update();

        /** No pending transactions here. Use this section for outgoing messages etc. Maximum delay to execution when
         * things are idle is SPICoprocessor::kSPITransactionTimeoutMs. **/

        // Print received data
        // pico.BlinkNetworkLED();
        // printf("Received: \r\n");
        // for (int i = 0; i < SPICoprocessor::kSPITransactionMaxLenBytes; i++) {
        //     printf("%02X ", spi_rx_transaction.buffer[i]);
        // }
        // printf("\r\n");
        // TODO: maybe convert to a SPITransaction type and fill in the transaction length property from t?
        // spi_rx_queue_.Push(spi_rx_transaction);

        // Yield to the idle task to avoid a watchdog trigger.
        vTaskDelay(1);  // Delay 1 tick (10ms).
    }

    ESP_LOGI("esp_spi_receive_task", "Received exit signal, ending SPI receive task.");
}