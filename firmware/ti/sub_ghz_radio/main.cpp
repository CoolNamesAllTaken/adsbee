#include <stdint.h>
#include <stddef.h>

// #include <NoRTOS.h>
#include <FreeRTOS.h>
#include "ti/drivers/Board.h"
#include <ti/drivers/GPIO.h>
#include <ti/drivers/dpl/ClockP.h>
// #include <ti/drivers/dma/UDMACC26XX.h>
#include "bsp.hh"
#include "spi_coprocessor.hh"
#include "spi_coprocessor_interface.hh"
#include "pico.hh"
#include "settings.hh"
#include "comms.hh"
#include "object_dictionary.hh"

/* Example/Board Header files */
// #include "ti_drivers_config.h"

// Example: https://dev.ti.com/tirex/explore/node?node=A__AGGwmqLCW-dNixEL.2NbnQ__com.ti.SIMPLELINK_CC13XX_CC26XX_SDK__BSEc4rl__LATEST

BSP bsp;
ObjectDictionary object_dictionary;
Pico pico_ll = Pico({});
SPICoprocessor pico = SPICoprocessor({.interface = pico_ll});
CommsManager comms_manager = CommsManager({});
SettingsManager settings_manager = SettingsManager();

extern void *mainThread(void *arg0);

#include <stdint.h>

#ifdef __ICCARM__
#include <DLib_Threads.h>
#endif

/* POSIX Header files */
#include <pthread.h>

/* RTOS header files */
#include <FreeRTOS.h>
#include <task.h>

#include <ti/drivers/Board.h>

extern void *mainThread(void *arg0);

/* Stack size in bytes */
#define THREADSTACKSIZE 1024

/*
 *  ======== main ========
 */
int main(void)
{
    pthread_t thread;
    pthread_attr_t attrs;
    struct sched_param priParam;
    int retc;

    /* initialize the system locks */
#ifdef __ICCARM__
    __iar_Initlocks();
#endif

    Board_init();

    /* Initialize the attributes structure with default values */
    pthread_attr_init(&attrs);

    /* Set priority, detach state, and stack size attributes */
    priParam.sched_priority = 1;
    retc = pthread_attr_setschedparam(&attrs, &priParam);
    retc |= pthread_attr_setdetachstate(&attrs, PTHREAD_CREATE_DETACHED);
    retc |= pthread_attr_setstacksize(&attrs, THREADSTACKSIZE);
    if (retc != 0)
    {
        /* failed to set attributes */
        while (1)
        {
        }
    }

    retc = pthread_create(&thread, &attrs, mainThread, NULL);
    if (retc != 0)
    {
        /* pthread_create() failed */
        while (1)
        {
        }
    }

    /* Start the FreeRTOS scheduler */
    vTaskStartScheduler();

    return (0);
}

// /*
//  *  ======== main ========
//  */
// int main(void)
// {
//     // NoRTOS_Config cfg;
//     // NoRTOS_getConfig(&cfg);
//     // cfg.clockTickPeriod = 100; // Set the system tick period to 10kHz (100us).
//     // cfg.swiIntNum = 11;        // Set the SWI interrupt number to 11 (SVCall).
//     // NoRTOS_setConfig(&cfg);

//     /* Call driver init functions */
//     Board_init();
//     GPIO_init();
//     SPI_init();

//     // Start NoRTOS AFTER system initialization.
//     NoRTOS_start();

//     // GPIO_setConfig(bsp.kSubGLEDPin, GPIO_CFG_OUT_STD | GPIO_CFG_OUT_LOW);

//     // Initialize the SPI coprocessor.
//     if (!pico.Init())
//     {
//         CONSOLE_ERROR("main", "Failed to initialize SPI coprocessor.");
//         return -1;
//     }

//     // pico.DeInit();

//     static const uint16_t kNumBlinks = 5;
//     for (uint16_t i = 0; i < kNumBlinks; ++i)
//     {
//         GPIO_write(bsp.kSubGLEDPin, 1);
//         ClockP_usleep(50000);
//         GPIO_write(bsp.kSubGLEDPin, 0);
//         ClockP_usleep(50000);
//     }

//     while (true)
//     {
//         pico.Update();
//         GPIO_write(bsp.kSubGLEDPin, 1);
//         ClockP_usleep(50000);
//         // sleep_ms_blocking(50);
//         GPIO_write(bsp.kSubGLEDPin, 0);
//         // sleep_ms_blocking(50);
//         ClockP_usleep(50000);
//     }

//     // /* Call mainThread function */
//     mainThread(NULL);

//     while (1)
//         ;
// }
