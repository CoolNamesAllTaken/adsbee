/* SPI Slave example, receiver (uses SPI Slave driver to communicate with sender)

   This example code is in the Public Domain (or CC0 licensed, at your option.)

   Unless required by applicable law or agreed to in writing, this
   software is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
   CONDITIONS OF ANY KIND, either express or implied.
*/
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "driver/gpio.h"
#include "driver/spi_slave.h"
#include "esp_log.h"
#include "esp_timer.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "spi_coprocessor.hh"

/*
SPI receiver (slave) example.

This example is supposed to work together with the SPI sender. It uses the standard SPI pins (MISO, MOSI, SCLK, CS) to
transmit data over in a full-duplex fashion, that is, while the master puts data on the MOSI pin, the slave puts its own
data on the MISO pin.

This example uses one extra pin: kHandshakeGPIOPin is used as a handshake pin. After a transmission has been set up and
we're ready to send/receive data, this code uses a callback to set the handshake pin high. The sender will detect this
and start sending a transaction. As soon as the transaction is done, the line gets set low again.
*/

/*
Pins in use. The SPI Master can use the GPIO mux, so feel free to change these if needed.
*/
// const gpio_num_t kMOSIGPIOPin = GPIO_NUM_35;
// const gpio_num_t kMISOGPIOPin = GPIO_NUM_36;
// const gpio_num_t kSCLKGPIOPin = GPIO_NUM_34;
// const gpio_num_t kCSGPIOPin = GPIO_NUM_33;
// const gpio_num_t kHandshakeGPIOPin = GPIO_NUM_0;
// const spi_host_device_t kSPIHost = SPI2_HOST; // HSPI
// const uint16_t kBufferSize = 1000;

// const gpio_num_t kESPLEDPin = GPIO_NUM_5;
// const uint32_t kESPLEDBlinkHalfPeriodMs = 1000;

// Called after a transaction is queued and ready for pickup by master. We use this to set the handshake line high.
// void esp_post_setup_cb(spi_slave_transaction_t *trans) { gpio_set_level(kHandshakeGPIOPin, 1); }

// // Called after transaction is sent/received. We use this to set the handshake line low.
// void esp_post_trans_cb(spi_slave_transaction_t *trans) { gpio_set_level(kHandshakeGPIOPin, 0); }

// void spi_receive_task(void *pvParameters) {
//     ESP_LOGI("spi_receive_task", "Started SPI receive task.");
//     // Buffer for received data
//     uint8_t spi_rx_buf[SPICoprocessor::kSPITransactionMaxLenBytes];

//     // Transaction structure
//     spi_slave_transaction_t t;
//     memset(&t, 0, sizeof(t));

//     // SPI slave transaction configuration
//     t.length = kBufferSize * 8;  // Transaction length is in bits
//     t.tx_buffer = NULL;          // We are not sending any data
//     t.rx_buffer = spi_rx_buf;    // Data will be received in this buffer

//     while (1) {
//         // Clear the receive buffer
//         memset(spi_rx_buf, 0, sizeof(spi_rx_buf));

//         // Wait for a transaction to complete
//         esp_err_t ret = spi_slave_transmit(kSPIHost, &t, portMAX_DELAY);
//         assert(ret == ESP_OK);

//         // Print received data
//         printf("Received: ");
//         for (int i = 0; i < kBufferSize; i++) {
//             printf("%02X ", spi_rx_buf[i]);
//         }
//         printf("\n");
//         gpio_set_level(kESPLEDPin, 1);
//         vTaskDelay(100 / portTICK_PERIOD_MS);
//         gpio_set_level(kESPLEDPin, 0);
//     }
// }

SPICoprocessor pico = SPICoprocessor({});

// void Init() { pico.Init(); }

// void Update() { pico.Update(); }

// Main application
extern "C" void app_main(void) {
    ESP_LOGI("app_main", "Beginning ADSBee Server Application.");
    pico.Init();
    while (1) {
        pico.Update();
    }

    // gpio_set_direction(kESPLEDPin, GPIO_MODE_OUTPUT);
    // bool esp_led_on = true;
    // gpio_set_level(kESPLEDPin, esp_led_on);
    // uint32_t last_esp_led_blink_timestamp_ms = esp_timer_get_time() / 1000;

    // // while (1)
    // // {
    // //     uint32_t timestamp_ms = esp_timer_get_time() / 1e3;
    // //     if (timestamp_ms > last_esp_led_blink_timestamp_ms + kESPLEDBlinkHalfPeriodMs)
    // //     {
    // //         ESP_LOGI("app_main", "Blink!");
    // //         esp_led_on = !esp_led_on;
    // //         gpio_set_level(kESPLEDPin, esp_led_on);
    // //         last_esp_led_blink_timestamp_ms = timestamp_ms;
    // //     }
    // // }
    // vTaskDelay(kESPLEDBlinkHalfPeriodMs / portTICK_PERIOD_MS);
    // gpio_set_level(kESPLEDPin, 0);

    // int n = 0;
    // esp_err_t ret;

    // // Configuration for the SPI bus
    // spi_bus_config_t buscfg = {
    //     .mosi_io_num = kMOSIGPIOPin,
    //     .miso_io_num = kMISOGPIOPin,
    //     .sclk_io_num = kSCLKGPIOPin,
    //     .quadwp_io_num = -1,
    //     .quadhd_io_num = -1,
    // };

    // // Configuration for the SPI slave interface
    // spi_slave_interface_config_t slvcfg = {.spics_io_num = kCSGPIOPin,
    //                                        .flags = 0,
    //                                        .queue_size = 3,
    //                                        .mode = 0,
    //                                        .post_setup_cb = esp_post_setup_cb,
    //                                        .post_trans_cb = esp_post_trans_cb};

    // // Configuration for the handshake line
    // gpio_config_t io_conf = {
    //     .pin_bit_mask = (1 << kHandshakeGPIOPin),
    //     .mode = GPIO_MODE_OUTPUT,
    //     .intr_type = GPIO_INTR_DISABLE,
    // };

    // // Configure handshake line as output
    // gpio_config(&io_conf);
    // // Enable pull-ups on SPI lines so we don't detect rogue pulses when no master is connected.
    // gpio_set_pull_mode(kMOSIGPIOPin, GPIO_PULLUP_ONLY);
    // // gpio_set_pull_mode(kSCLKGPIOPin, GPIO_PULLUP_ONLY);
    // gpio_set_pull_mode(kCSGPIOPin, GPIO_PULLUP_ONLY);

    // // Initialize SPI slave interface
    // ret = spi_slave_initialize(kSPIHost, &buscfg, &slvcfg, SPI_DMA_CH_AUTO);
    // assert(ret == ESP_OK);

    // WORD_ALIGNED_ATTR char sendbuf[129] = "";
    // WORD_ALIGNED_ATTR char spi_rx_buf[129] = "";
    // memset(spi_rx_buf, 0, 33);
    // spi_slave_transaction_t t;
    // memset(&t, 0, sizeof(t));

    // // gpio_set_direction(kESPLEDPin, GPIO_MODE_OUTPUT);
    // // bool esp_led_on = true;
    // // gpio_set_level(kESPLEDPin, esp_led_on);
    // // uint32_t last_esp_led_blink_timestamp_ms = esp_timer_get_time() / 1000;

    // xTaskCreate(spi_receive_task, "spi_receive_task", 4096, NULL, 10, NULL);

    // while (1) {
    //     ESP_LOGI("app_main", "In app main loop.");
    //     vTaskDelay(1000 / portTICK_PERIOD_MS);
    //     // uint32_t timestamp_ms = esp_timer_get_time() / 1e3;
    //     // if (timestamp_ms > last_esp_led_blink_timestamp_ms + kESPLEDBlinkHalfPeriodMs)
    //     // {
    //     //     ESP_LOGI("app_main", "Blink!");
    //     //     esp_led_on = !esp_led_on;
    //     //     gpio_set_level(kESPLEDPin, esp_led_on);
    //     //     last_esp_led_blink_timestamp_ms = timestamp_ms;
    //     // }

    //     // // Clear receive buffer, set send buffer to something sane
    //     // memset(spi_rx_buf, 0xA5, 129);
    //     // sprintf(sendbuf, "This is the receiver, sending data for transmission number %04d.", n);

    //     // // Set up a transaction of 128 bytes to send/receive
    //     // t.length = 128 * 8;
    //     // t.tx_buffer = sendbuf;
    //     // t.rx_buffer = spi_rx_buf;
    //     // /* This call enables the SPI slave interface to send/receive to the sendbuf and spi_rx_buf. The
    //     transaction
    //     // is initialized by the SPI master, however, so it will not actually happen until the master starts a
    //     hardware
    //     // transaction by pulling CS low and pulsing the clock etc. In this specific example, we use the handshake
    //     line,
    //     // pulled up by the .post_setup_cb callback that is called as soon as a transaction is ready, to let the
    //     master
    //     // know it is free to transfer data.
    //     // */
    //     // ret = spi_slave_transmit(kSPIHost, &t, portMAX_DELAY);

    //     // // spi_slave_transmit does not return until the master has done a transmission, so by here we have sent
    //     our
    //     // data and
    //     // // received data from the master. Print it.
    //     // printf("Received: %s\n", spi_rx_buf);
    //     // n++;
    // }
}
