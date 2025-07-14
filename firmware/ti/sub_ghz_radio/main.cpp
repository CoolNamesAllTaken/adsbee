#include <stdint.h>
#include <stddef.h>

extern "C"
{
#include "NoRTOS.h"
#include "ti/drivers/Board.h"
#include "ti/drivers/GPIO.h"
#include "ti/drivers/SPI.h"
#include <posix/unistd.h>
}
// #include <ti/drivers/dma/UDMACC26XX.h>

#include "bsp.hh"
#include "spi_coprocessor.hh"
#include "spi_coprocessor_interface.hh"
#include "pico.hh"
#include "settings.hh"
#include "comms.hh"
#include "object_dictionary.hh"

#include "unistd.h" // For usleep.

BSP bsp;
ObjectDictionary object_dictionary;
Pico pico_ll = Pico({});
SPICoprocessor pico = SPICoprocessor({.interface = pico_ll});
CommsManager comms_manager = CommsManager({});
SettingsManager settings_manager = SettingsManager();

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
    // NoRTOS_Config cfg;
    // NoRTOS_getConfig(&cfg);
    // cfg.clockTickPeriod = 100; // Set the system tick period to 10kHz (100us).
    // cfg.swiIntNum = 11;        // Set the SWI interrupt number to 11 (SVCall).
    // NoRTOS_setConfig(&cfg);

    /* Call driver init functions */
    Board_init();
    SPI_init();

    // Start NoRTOS AFTER system initialization.
    NoRTOS_start();

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

    while (true)
    {
        pico_ll.Update();
        GPIO_write(bsp.kSubGLEDPin, 1);
        usleep(50000); // 50ms
        GPIO_write(bsp.kSubGLEDPin, 0);
        usleep(50000); // 50ms
    }
}