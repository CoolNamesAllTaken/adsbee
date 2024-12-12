#include "comms.hh"
#include "driver/spi_master.h"
#include "esp_check.h"
#include "esp_eth_driver.h"
#include "esp_event.h"
#include "esp_log.h"
#include "esp_mac.h"
#include "esp_netif.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "sdkconfig.h"

/** "Pass-Through" functions used to access member functions in callbacks. **/
void ethernet_event_handler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data) {
    comms_manager.EthernetEventHandler(arg, event_base, event_id, event_data);
}
/** End "Pass-Through" functions. **/

bool CommsManager::EthernetDeInit() {
    if (!wifi_was_initialized_) return true;  // Don't try de-initializing if it was never initialized.

    // The de-init functions are not yet supported by ESP IDF, so the best bet is to just restart.
    esp_restart();  // Software reset.
    return false;   // abort didn't work
}

void CommsManager::EthernetEventHandler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data) {
    uint8_t mac_addr[6] = {0};
    esp_eth_handle_t eth_handle = *(esp_eth_handle_t*)event_data;

    switch (event_id) {
        case ETHERNET_EVENT_CONNECTED:
            esp_eth_ioctl(eth_handle, ETH_CMD_G_MAC_ADDR, mac_addr);
            CONSOLE_INFO("CommsManager::EthernetEventHandler", "Ethernet Link Up");
            CONSOLE_INFO("CommsManager::EthernetEventHandler", "Ethernet HW Addr %02x:%02x:%02x:%02x:%02x:%02x",
                         mac_addr[0], mac_addr[1], mac_addr[2], mac_addr[3], mac_addr[4], mac_addr[5]);
            break;
        case ETHERNET_EVENT_DISCONNECTED:
            CONSOLE_INFO("CommsManager::EthernetEventHandler", "Ethernet Link Down");
            break;
        case ETHERNET_EVENT_START:
            CONSOLE_INFO("CommsManager::EthernetEventHandler", "Ethernet Started");
            break;
        case ETHERNET_EVENT_STOP:
            CONSOLE_INFO("CommsManager::EthernetEventHandler", "Ethernet Stopped");
            break;
        default:
            break;
    }
}

bool CommsManager::EthernetInit() {
    //  Create instance(s) of esp-netif for SPI Ethernet(s)
    esp_netif_config_t cfg = ESP_NETIF_DEFAULT_ETH();
    ethernet_netif_ = esp_netif_new(&cfg);

    // ESP_ERROR_CHECK(esp_netif_set_hostname(ethernet_netif_, hostname));

    // Register user defined event handers
    ESP_ERROR_CHECK(esp_event_handler_register(ETH_EVENT, ESP_EVENT_ANY_ID, &ethernet_event_handler, NULL));
    if (!ip_event_handler_was_initialized_) {
        IPInit();
    }

    // SPI bus configuration.
    spi_bus_config_t buscfg = {
        .mosi_io_num = config_.aux_spi_mosi_pin,
        .miso_io_num = config_.aux_spi_miso_pin,
        .sclk_io_num = config_.aux_spi_clk_pin,
        .quadwp_io_num = -1,
        .quadhd_io_num = -1,
    };

    // W5500 SPI device configuration.
    spi_device_interface_config_t spi_devcfg = {

        .command_bits = 16,  // Actually it's the address phase in W5500 SPI frame
        .address_bits = 8,   // Actually it's the control phase in W5500 SPI frame
        .dummy_bits = 0,
        .mode = 0,
        .clock_source = SPI_CLK_SRC_DEFAULT,
        .clock_speed_hz = config_.aux_spi_clk_rate_hz,
        .input_delay_ns = 0,
        .spics_io_num = config_.aux_spi_cs_pin,
        .flags = 0,
        .queue_size = 20,
        .pre_cb = nullptr,
        .post_cb = nullptr,
    };

    eth_w5500_config_t w5500_config = ETH_W5500_DEFAULT_CONFIG(config_.aux_spi_handle, &spi_devcfg);
    w5500_config.int_gpio_num = config_.aux_io_c_pin;
    // TODO: no reset pin?

    // Init MAC and PHY configs to default
    eth_mac_config_t mac_config = ETH_MAC_DEFAULT_CONFIG();
    eth_phy_config_t phy_config = ETH_PHY_DEFAULT_CONFIG();
    phy_config.reset_gpio_num = -1;  // PHY reset is controlled by MAC.

    esp_err_t ret = gpio_install_isr_service(0);
    if (ret == ESP_ERR_INVALID_STATE) {
        // ISR handler has been already installed so no issues
        CONSOLE_INFO("CommsManager::EthernetInit", "GPIO ISR handler has been already installed");
    } else if (ret != ESP_OK) {
        CONSOLE_ERROR("CommsManager::EthernetInit", "GPIO ISR handler install failed");
        return false;
    }

    ESP_ERROR_CHECK(spi_bus_initialize(config_.aux_spi_handle, &buscfg, SPI_DMA_CH_AUTO));
    esp_eth_mac_t* mac = esp_eth_mac_new_w5500(&w5500_config, &mac_config);
    esp_eth_phy_t* phy = esp_eth_phy_new_w5500(&phy_config);

    esp_eth_config_t eth_config = ETH_DEFAULT_CONFIG(mac, phy);
    esp_eth_handle_t eth_handle = NULL;
    ESP_ERROR_CHECK(esp_eth_driver_install(&eth_config, &eth_handle));

    // Attach Ethernet driver to TCP/IP stack
    ESP_ERROR_CHECK(esp_netif_attach(ethernet_netif_, esp_eth_new_netif_glue(eth_handle)));

    // Start Ethernet driver
    ESP_ERROR_CHECK(esp_eth_start(eth_handle));

    return true;

    // phy_config.autonego_timeout_ms = 0;
    // phy_config.reset_gpio_num = config_.aux_io_b_pin;
    // phy_config.phy_addr = -1;  // Enable PHY address detection during initialization.

    // esp_err_t ret = gpio_install_isr_service(0);
    // if (ret == ESP_ERR_INVALID_STATE) {
    //     // ISR handler has been already installed so no issues
    //     CONSOLE_INFO("CommsManager::EthernetInit", "GPIO ISR handler has been already installed");
    // } else if (ret != ESP_OK) {
    //     CONSOLE_ERROR("CommsManager::EthernetInit", "GPIO ISR handler install failed");
    //     return false;
    // }

    // // Configure SPI interface and Ethernet driver for specific SPI module
    // esp_eth_mac_t* mac_spi;
    // esp_eth_phy_t* phy_spi;
    // esp_eth_handle_t eth_handle_spi = NULL;

    // // Set remaining GPIO numbers and configuration used by the SPI module.

    // mac_spi = esp_eth_mac_new_w5500(&w5500_config, &mac_config);
    // phy_spi = esp_eth_phy_new_w5500(&phy_config);

    // esp_eth_config_t eth_config_spi = ETH_DEFAULT_CONFIG(mac_spi, phy_spi);
    // ESP_ERROR_CHECK(esp_eth_driver_install(&eth_config_spi, &eth_handle_spi));

    // uint8_t mac_addr[6];
    // esp_read_mac(mac_addr, ESP_MAC_ETH);

    // ESP_ERROR_CHECK(esp_eth_ioctl(eth_handle_spi, ETH_CMD_S_MAC_ADDR, mac_addr));

    // // attach Ethernet driver to TCP/IP stack
    // ESP_ERROR_CHECK(esp_netif_attach(ethernet_netif_, esp_eth_new_netif_glue(eth_handle_spi)));

    // /* start Ethernet driver state machine */
    // ESP_ERROR_CHECK(esp_eth_start(eth_handle_spi));

    // return true;
}