#include <stdint.h>
#include <stddef.h>

#include <NoRTOS.h>
#include <ti/drivers/GPIO.h>
#include <ti/drivers/dpl/ClockP.h>
#include "bsp.hh"

BSP bsp;

/* Example/Board Header files */
#include "ti_drivers_config.h"

extern void *mainThread(void *arg0);

/*
 *  ======== main ========
 */
int main(void)
{
    /* Call driver init functions */
    Board_initGeneral();
    GPIO_init();

    /* Start NoRTOS */
    NoRTOS_start();

    GPIO_setConfig(bsp.kSubGLEDPin, GPIO_CFG_OUT_STD);

    static const uint16_t kNumBlinks = 20;
    for (uint16_t i = 0; i < kNumBlinks; ++i)
    {
        GPIO_write(bsp.kSubGLEDPin, 1);
        ClockP_usleep(500000);
        GPIO_write(bsp.kSubGLEDPin, 0);
        ClockP_usleep(500000);
    }

    // /* Call mainThread function */
    mainThread(NULL);

    while (1)
        ;
}
