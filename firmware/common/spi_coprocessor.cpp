#include "spi_coprocessor.hh"

#include "buffer_utils.hh"

#ifdef ON_PICO
#include "hardware/gpio.h"
#else
WORD_ALIGNED_ATTR SPICoprocessor::SPITransaction spi_rx_transaction;
WORD_ALIGNED_ATTR SPICoprocessor::SPITransaction spi_tx_transaction;

// Called after a transaction is queued and ready for pickup by master. We use this to set the handshake line high.
void esp_spi_post_setup_cb(spi_slave_transaction_t *trans) { pico.SetSPIHandshakePinLevel(1); }

// Called after transaction is sent/received. We use this to set the handshake line low.
void esp_spi_post_trans_cb(spi_slave_transaction_t *trans) { pico.SetSPIHandshakePinLevel(0); }

void esp_spi_receive_task(void *pvParameters) {
    pico.SPIReceiveTask();  // Only returns during DeInit.
    vTaskDelete(NULL);      // Delete this task.
}

void SPICoprocessor::SPIReceiveTask() {
    ESP_LOGI("SPICoprocessor::SPIReceiveTask", "Started SPI receive task.");

    // Transaction structure
    spi_slave_transaction_t t;
    memset(&t, 0, sizeof(t));

    t.length = SPICoprocessor::kSPITransactionMaxLenBytes;  // Transaction length is in bits
    t.tx_buffer = NULL;                                     // We are not sending any data
    t.rx_buffer = spi_rx_transaction.buffer;                // Data will be received in this buffer

    ESP_LOGI("SPICoprocessor::SPIReceiveTask", "Reached main loop.");

    while (!spi_receive_task_should_exit_) {
        // Clear the receive buffer
        memset(spi_rx_transaction.buffer, 0, kSPITransactionMaxLenBytes);

        // Wait for a transaction to complete
        esp_err_t status = spi_slave_transmit(config_.spi_handle, &t, SPICoprocessor::kSPIRxTimeoutTicks);
        if (status != ESP_OK) {
            if (status == ESP_ERR_TIMEOUT) {
                // Timeout is no big deal, just try again.
                continue;
            } else {
                ESP_LOGE("esp_spi_receive_task", "SPI transaction failed unexpectedly with code %d.", status);
                continue;
            }
        }

        // Print received data
        BlinkNetworkLED();
        printf("Received: ");
        for (int i = 0; i < SPICoprocessor::kSPITransactionMaxLenBytes; i++) {
            printf("%02X ", spi_rx_transaction.buffer[i]);
        }
        printf("\n");
        spi_rx_queue_.Push(spi_rx_transaction);
    }

    ESP_LOGI("esp_spi_receive_task", "Received exit signal, ending SPI receive task.");
}

#endif

bool SPICoprocessor::SCMessage::IsValid(uint32_t received_length) {
    if (received_length != length) {
        return false;
    }
    if (calculate_crc16((uint8_t *)&length, length - sizeof(crc)) != crc) {
        return false;
    }
    return true;
}

void SPICoprocessor::SCMessage::PopulateCRCAndLength(uint32_t payload_length) {
    length = payload_length + sizeof(SCMessage);
    // CRC calculation starts after the CRC itself.
    crc = calculate_crc16((uint8_t *)(&length), payload_length + sizeof(SCMessage) - sizeof(crc));
}

/** SCMessage Constructors **/

SPICoprocessor::SettingsMessage::SettingsMessage(const SettingsManager::Settings &settings_in) {
    type = kSCPacketTypeSettings;
    settings = settings_in;
    PopulateCRCAndLength(sizeof(SettingsMessage) - sizeof(SCMessage));
}

SPICoprocessor::AircraftListMessage::AircraftListMessage(uint16_t num_aicraft_in, const Aircraft aircraft_list_in[]) {
    type = kSCPacketTypeAircraftList;
    num_aicraft = num_aicraft_in;
    // Copy over the aircraft that we are tracking.
    for (uint16_t i = 0; i < num_aicraft; i++) {
        aircraft_list[i] = aircraft_list_in[i];
    }
    // Set the rest of the aircraft list to 0's.
    for (uint16_t i = num_aicraft; i < AircraftDictionary::kMaxNumAircraft; i++) {
        aircraft_list[i] = Aircraft();
    }
    // memset(&(aircraft_list[num_aicraft]), 0, sizeof(Aircraft) * (AircraftDictionary::kMaxNumAircraft - num_aicraft));
    PopulateCRCAndLength(sizeof(AircraftListMessage) - sizeof(SCMessage));
}

bool SPICoprocessor::Init() {
    bool ret = true;

#ifdef ON_PICO
#else
    ret &= gpio_set_direction(config_.network_led_pin, GPIO_MODE_OUTPUT);
#endif
    ret &= SPIInit();
    return ret;
}

bool SPICoprocessor::DeInit() {
    bool ret = true;
    ret &= SPIDeInit();
    return ret;
}

bool SPICoprocessor::Update() {
#ifdef ON_PICO
#else
    UpdateNetworkLED();
#endif

    return true;
}

bool SPICoprocessor::SendMessage(SCMessage &message) {
    // TODO: Convert all writes to write / reads. First byte read should be the transaction length. Rest of the
    // transaction needs to be a for loop that sends kSPIMaxTransferLengthBytes each time.
#ifdef ON_PICO
    gpio_put(config_.spi_cs_pin, 0);
    uint8_t *tx_buf = reinterpret_cast<uint8_t *>(&message);
    spi_write_blocking(config_.spi_handle, tx_buf, message.length);
    gpio_put(config_.spi_cs_pin, 1);
#else
#endif
    return true;
}

bool SPICoprocessor::SPIInit() {
#ifdef ON_PICO
    // ESP32 chip select pin.
    gpio_init(config_.spi_cs_pin);
    gpio_set_dir(config_.spi_cs_pin, GPIO_OUT);
    gpio_put(config_.spi_cs_pin, 0);
    // ESP32 handshake pin.
    gpio_init(config_.spi_handshake_pin);
    gpio_set_dir(config_.spi_handshake_pin, GPIO_IN);
    gpio_set_pulls(config_.spi_handshake_pin, true, false);  // Handshake pin is pulled up.
    // ESP32 SPI pins.
    gpio_set_function(config_.spi_clk_pin, GPIO_FUNC_SPI);
    gpio_set_function(config_.spi_mosi_pin, GPIO_FUNC_SPI);
    gpio_set_function(config_.spi_miso_pin, GPIO_FUNC_SPI);

    // Initialize SPI Peripheral.
    spi_init(config_.spi_handle, config_.clk_rate_hz);
    spi_set_format(config_.spi_handle,
                   8,           // Bits per transfer.
                   SPI_CPOL_1,  // Polarity (CPOL).
                   SPI_CPHA_1,  // Phase (CPHA).
                   SPI_MSB_FIRST);
#else
    spi_bus_config_t spi_buscfg = {
        .mosi_io_num = config_.spi_mosi_pin,
        .miso_io_num = config_.spi_miso_pin,
        .sclk_io_num = config_.spi_clk_pin,
        .quadwp_io_num = -1,
        .quadhd_io_num = -1,
    };
    spi_slave_interface_config_t spi_slvcfg = {.spics_io_num = config_.spi_cs_pin,
                                               .flags = 0,
                                               .queue_size = 3,
                                               .mode = 0,
                                               .post_setup_cb = esp_spi_post_setup_cb,
                                               .post_trans_cb = esp_spi_post_trans_cb};
    gpio_config_t handshake_io_conf = {
        .pin_bit_mask = (static_cast<uint64_t>(0b1) << config_.spi_handshake_pin),
        .mode = GPIO_MODE_OUTPUT,
        .intr_type = GPIO_INTR_DISABLE,
    };
    gpio_config(&handshake_io_conf);
    gpio_set_pull_mode(config_.spi_mosi_pin, GPIO_PULLUP_ONLY);
    gpio_set_pull_mode(config_.spi_miso_pin, GPIO_PULLUP_ONLY);
    gpio_set_pull_mode(config_.spi_cs_pin, GPIO_PULLUP_ONLY);

    esp_err_t status = spi_slave_initialize(config_.spi_handle, &spi_buscfg, &spi_slvcfg, SPI_DMA_CH_AUTO);
    if (status != ESP_OK) {
        ESP_LOGE("SPICoprocessor::SPIInit", "SPI initialization failed with code %d.", status);
    }

    spi_receive_task_should_exit_ = false;
    xTaskCreate(esp_spi_receive_task, "spi_receive_task", kSPIRxTaskStackDepthBytes, NULL, 10, NULL);

#endif
    return true;
}

bool SPICoprocessor::SPIDeInit() {
#ifdef ON_PICO
    // ESP32 chip select pin.
    gpio_deinit(config_.spi_cs_pin);
    // ESP32 handshake pin.
    gpio_deinit(config_.spi_handshake_pin);

    // De-initialize SPI Peripheral.
    spi_deinit(config_.spi_handle);
#else
    spi_receive_task_should_exit_ = true;
#endif
    return true;
}

int SPICoprocessor::SPIWriteBlocking(uint8_t *tx_buf, uint32_t length) {
#ifdef ON_PICO
    return spi_write_blocking(config_.spi_handle, tx_buf, length);
#else

#endif
    return -1;
}

int SPICoprocessor::SPIReadBlocking(uint8_t *rx_buf, uint32_t length) {
#ifdef ON_PICO
    return spi_read_blocking(config_.spi_handle, 0, rx_buf, length);
#else

#endif
    return -1;
}