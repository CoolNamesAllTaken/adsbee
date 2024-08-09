#ifndef SPI_COPROCESSOR_HH_
#define SPI_COPROCESSOR_HH_

#include "aircraft_dictionary.hh"
#include "settings.hh"
#include "transponder_packet.hh"

#ifdef ON_PICO
#include "hardware/spi.h"
#elif ON_ESP32
#include "data_structures.hh"
#include "driver/gpio.h"
#include "driver/spi_slave.h"
#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#endif

class SPICoprocessor {
   public:
    static const uint16_t kSPITransactionMaxLenBytes = 1000;
    static_assert(kSPITransactionMaxLenBytes % 4 == 0);  // Make sure it's word-aligned.
    static const uint16_t kSPITransactionQueueLenTransactions = 3;

    struct SPITransaction {
        uint8_t buffer[kSPITransactionMaxLenBytes];

        SPITransaction() {
            for (uint16_t i = 0; i < kSPITransactionMaxLenBytes; i++) {
                // ESP_LOGI("SPITransaction", "Clearing i=%d", i);
                buffer[i] = 0x0;
            }
        }
    };

#ifdef ON_PICO
#elif ON_ESP32
    static const uint32_t kNetworkLEDBLinkDurationMs = 1000;
    static const uint32_t kSPIRxTaskStackDepthBytes = 4096;
    static const TickType_t kSPIRxTimeoutTicks = 100 / portTICK_PERIOD_MS;
#endif
    struct SPICoprocessorConfig {
        uint32_t clk_rate_hz = 40e6;  // 40 MHz
#ifdef ON_PICO
        spi_inst_t *spi_handle = spi1;
        uint16_t spi_clk_pin = 10;
        uint16_t spi_mosi_pin = 11;
        uint16_t spi_miso_pin = 12;
        uint16_t spi_cs_pin = 9;
        uint16_t spi_handshake_pin = 13;
#elif ON_ESP32
        spi_host_device_t spi_handle = SPI2_HOST;
        gpio_num_t spi_mosi_pin = GPIO_NUM_35;
        gpio_num_t spi_miso_pin = GPIO_NUM_36;
        gpio_num_t spi_clk_pin = GPIO_NUM_34;
        gpio_num_t spi_cs_pin = GPIO_NUM_33;
        gpio_num_t spi_handshake_pin = GPIO_NUM_0;

        gpio_num_t network_led_pin = GPIO_NUM_5;
#endif
    };

    enum PacketType : int8_t {
        kSCPacketTypeInvalid = -1,
        kSCPacketTypeSettings,
        kSCPacketTypeNetworkMessage,
        kSCPacketTypeAircraftList
    };

    struct SCMessage {
        uint16_t crc;     // 16-bit CRC of all bytes after the CRC.
        uint32_t length;  // Length of the packet in bytes.
        SPICoprocessor::PacketType type;

        /**
         * Checks to see if a SPICoprocessor packet (SCMessage) is valid.
         * @param[in] received_length Number of bytes received over SPI.
         * @retval True if packet is valid, false otherwise.
         */
        bool IsValid(uint32_t received_length);

        /**
         * Sets the packet length and CRC based on the payload. CRC is calculated for everything after the CRC itself.
         * @param[in] payload_length Number of bytes in the payload, which begins right after length for packets that
         * inherit from SCMessage.
         */
        void PopulateCRCAndLength(uint32_t payload_length);
    };

    struct SettingsMessage : public SCMessage {
        SettingsManager::Settings settings;

        /**
         * SettingsMessage constructor. Populates the settings and adds length, packet type, and CRC info to parent.
         * @param[in] settings Reference to a SettingsManager::Settings struct to send over.
         * @retval The constructed Settings Packet.
         */
        SettingsMessage(const SettingsManager::Settings &settings_in);
    };

    struct AircraftListMessage : public SCMessage {
        uint16_t num_aicraft;
        Aircraft aircraft_list[AircraftDictionary::kMaxNumAircraft];

        /**
         * AircraftListMessage constructor. Populates the aircraft list and adds length, packet type, and CRC info to
         * parent.
         * @param[in] num_aircraft Number of aircraft in the list. Determines the length of the packet.
         * @param[in] aircraft_list Array of Aircraft objects.
         * @retval The constructed AircraftListMessage.
         */
        AircraftListMessage(uint16_t num_aicraft_in, const Aircraft aircraft_list_in[]);
    };

    struct DecodedTransponderPacketMessage : public SCMessage {
        DecodedTransponderPacket packet;

        /**
         * DecodedTransponderPacketMessage constructor. Populates the packet to send and adds length, packet type, and
         * CRC info to parent.
         * @param[in] packet Reference to transponder packet to use for construction.
         */
        DecodedTransponderPacketMessage(const DecodedTransponderPacket &packet_in) {
            packet = packet_in;
            PopulateCRCAndLength(sizeof(DecodedTransponderPacketMessage) - sizeof(SCMessage));
        }
    };

    struct RawTransponderPacketMessage : public SCMessage {
        RawTransponderPacket packet;

        RawTransponderPacketMessage(const RawTransponderPacket &packet_in) {
            packet = packet_in;
            PopulateCRCAndLength(sizeof(RawTransponderPacketMessage) - sizeof(SCMessage));
        }
    };

    // NOTE: Pico (leader) and ESP32 (follower) will have different behaviors for these functions.
    bool Init();
    bool DeInit();
    bool Update();

    /**
     * Transmit a packet to the coprocessor. Blocking.
     * @param[in] packet Reference to the packet that will be transmitted.
     * @retval True if succeeded, false otherwise.
     */
    bool SendMessage(SCMessage &message);

#ifdef ON_PICO
#elif ON_ESP32
    /**
     * Helper function used by callbacks to set the handshake pin high or low on the ESP32.
     */
    void SetSPIHandshakePinLevel(bool level) { gpio_set_level(config_.spi_handshake_pin, level); }

    /**
     * Function called from the task spawned during Init().
     */
    void SPIReceiveTask();

    /**
     * Turns on the network LED for a specified number of milliseconds. Relies on the UpdateNetowrkLED() function to
     * turn the lED off.
     * @param[in] blink_duration_ms Number of milliseconds that the LED should stay on for.
     */
    void BlinkNetworkLED(uint16_t blink_duration_ms = kNetworkLEDBLinkDurationMs) {
        gpio_set_level(config_.network_led_pin, 1);
        network_led_turn_off_timestamp_ticks_ = xTaskGetTickCount() + kNetworkLEDBLinkDurationMs / portTICK_PERIOD_MS;
    }

    /**
     * Turns off the network LED if necessary.
     */
    void UpdateNetworkLED() {
        if (xTaskGetTickCount() > network_led_turn_off_timestamp_ticks_) {
            gpio_set_level(config_.network_led_pin, 0);
        }
    }
#endif

   private:
    bool SPIInit();
    bool SPIDeInit();
    int SPIWriteBlocking(uint8_t *tx_buf, uint32_t length);
    int SPIReadBlocking(uint8_t *rx_buf, uint32_t length);

    SPICoprocessorConfig config_;

#ifdef ON_PICO
#elif ON_ESP32
    WORD_ALIGNED_ATTR SPITransaction spi_rx_queue_buf_[kSPITransactionQueueLenTransactions];
    WORD_ALIGNED_ATTR SPITransaction spi_tx_queue_buf_[kSPITransactionQueueLenTransactions];

    PFBQueue<SPITransaction> spi_rx_queue_ = PFBQueue<SPITransaction>(
        {.buf_len_num_elements = kSPITransactionQueueLenTransactions, .buffer = spi_rx_queue_buf_});
    PFBQueue<SPITransaction> spi_tx_queue_ = PFBQueue<SPITransaction>(
        {.buf_len_num_elements = kSPITransactionQueueLenTransactions, .buffer = spi_tx_queue_buf_});

    bool spi_receive_task_should_exit_ = false;  // Flag used to tell SPI receive task to exit.
    TickType_t network_led_turn_off_timestamp_ticks_ = 0;
#endif
};

#ifdef ON_PICO
extern SPICoprocessor esp32;
#elif ON_ESP32
extern SPICoprocessor pico;
#endif

#endif /* SPI_COPROCESSOR_HH_ */