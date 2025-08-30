#include <stdint.h>
#include <stddef.h>

extern "C"
{
// Make sure these are linked in C.
#include "NoRTOS.h"
#include "ti/drivers/Board.h"
#include "ti/drivers/GPIO.h"
#include "ti/drivers/SPI.h"
#include "ti/drivers/Power.h"
#include <posix/unistd.h>
}

#include "bsp.hh"
#include "spi_coprocessor.hh"
#include "spi_coprocessor_interface.hh"
#include "pico.hh"
#include "settings.hh"
#include "comms.hh"
#include "object_dictionary.hh"
#include "sub_ghz_radio.hh"
#include "uat_packet_decoder.hh"

// #include "unistd.h" // For usleep.
#include <cstring> // For malloc

BSP bsp;
ObjectDictionary object_dictionary;
Pico pico_ll = Pico({});
SPICoprocessor pico = SPICoprocessor({.interface = pico_ll});
CommsManager comms_manager = CommsManager({});
SettingsManager settings_manager = SettingsManager();
SubGHzRadio subg_radio = SubGHzRadio({});
UATPacketDecoder uat_packet_decoder = UATPacketDecoder();

/**
 * A note on interrupt priorities (configured via Sysconfig):
 *
 * SPI peripheral:
 *  Hardware priority: Must be HIGHER than DMA.
 *  Software priority: Must be very low, not sure why. Hardfaults will occur otherwise.
 * DMA: Must be LOWER than SPI hardware interrupt priority.
 */

void exception_handler()
{
    while (1)
    {
    }
}

/*
 *  ======== main ========
 */
int main(void)
{
    Power_disablePolicy(); // Stop aggressive clock gating that messes with the debugger.

    NoRTOS_Config cfg;
    NoRTOS_getConfig(&cfg);
    cfg.clockTickPeriod = 100; // Set the system tick period to 10kHz (100us).
    NoRTOS_setConfig(&cfg);

    /* Call driver init functions */
    Board_init();
    SPI_init();

    // Start NoRTOS AFTER system initialization.
    NoRTOS_start();

    // Log everything until we hear otherwise.
    settings_manager.settings.log_level = SettingsManager::LogLevel::kInfo;

    static const uint16_t kNumBlinks = 2;
    for (uint16_t i = 0; i < kNumBlinks; ++i)
    {
        GPIO_write(bsp.kSubGLEDPin, 1);
        usleep(50000); // 50ms
        GPIO_write(bsp.kSubGLEDPin, 0);
        usleep(50000); // 50ms
    }

    // Initialize the SPI coprocessor.
    if (!pico.Init())
    {
        CONSOLE_ERROR("main", "Failed to initialize SPI coprocessor.");
        exception_handler();
    }
    CONSOLE_INFO("main", "SPI coprocessor initialized successfully.");

    // Blocking wait for master to provide settings data.
    settings_manager.settings.settings_version = UINT32_MAX;
    object_dictionary.RequestSCCommand(ObjectDictionary::SCCommandRequestWithCallback{
        .request =
            ObjectDictionary::SCCommandRequest{.command = ObjectDictionary::SCCommand::kCmdWriteToSlaveRequireAck,
                                               .addr = ObjectDictionary::Address::kAddrSettingsData,
                                               .offset = 0,
                                               .len = sizeof(SettingsManager::Settings)},
        .complete_callback =
            []() {},
    });
    // Wait for settings data to be received.
    while (settings_manager.settings.settings_version == UINT32_MAX)
    {
    }
    CONSOLE_INFO("ADSBeeServer::Init", "Settings data read from Pico.");
    // settings_manager.Print();

    if (!subg_radio.Init())
    {
        CONSOLE_ERROR("main", "Failed to initialize SubGHz radio.");
        exception_handler();
    }
    CONSOLE_INFO("main", "SubGHz radio initialized successfully.");

    while (true)
    {
        pico.UpdateLED();
        uat_packet_decoder.Update();
    }
}