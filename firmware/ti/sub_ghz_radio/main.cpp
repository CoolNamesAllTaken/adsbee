#include <stdint.h>
#include <stddef.h>

#include <NoRTOS.h>
#include <ti/drivers/GPIO.h>
#include <ti/drivers/dpl/ClockP.h>
#include "bsp.hh"
#include "spi_coprocessor.hh"
#include "spi_coprocessor_interface.hh"
#include "pico.hh"
#include "settings.hh"
#include "comms.hh"
#include "object_dictionary.hh"

/* Example/Board Header files */
#include "ti_drivers_config.h"

BSP bsp;
ObjectDictionary object_dictionary;
Pico pico_ll = Pico({});
SPICoprocessor pico = SPICoprocessor({.interface = pico_ll});
CommsManager comms_manager = CommsManager({});
SettingsManager settings_manager = SettingsManager();

extern void *mainThread(void *arg0);

/*
 *  ======== main ========
 */
int main(void)
{
    /* Call driver init functions */
    Board_init();

    /* Start NoRTOS */
    NoRTOS_start();

    // GPIO_setConfig(bsp.kSubGLEDPin, GPIO_CFG_OUT_STD);

    static const uint16_t kNumBlinks = 5;
    for (uint16_t i = 0; i < kNumBlinks; ++i)
    {
        GPIO_write(bsp.kSubGLEDPin, 1);
        ClockP_usleep(50000);
        GPIO_write(bsp.kSubGLEDPin, 0);
        ClockP_usleep(50000);
    }

    // Initialize the SPI coprocessor.
    if (!pico.Init())
    {
        CONSOLE_ERROR("main", "Failed to initialize SPI coprocessor.");
        return -1;
    }

    while (true)
    {
        GPIO_write(bsp.kSubGLEDPin, 1);
        ClockP_usleep(50000);
        GPIO_write(bsp.kSubGLEDPin, 0);
        ClockP_usleep(50000);
    }

    // /* Call mainThread function */
    mainThread(NULL);

    while (1)
        ;
}
