/** Make a new version of NoRTOS that's C++ safe. **/

// #include <ti/drivers/dpl/ClockP.h>
// #include <ti/drivers/dpl/HwiP.h>
// #include <ti/drivers/dpl/SemaphoreP.h>
#include <unistd.h>

#include "NoRTOS.h"

extern uint32_t ClockP_tickPeriod;

/*
 *  ======== NoRTOS_getConfig ========
 */
void NoRTOS_getConfig(NoRTOS_Config *cfg)
{
    cfg->idleCallback = SemaphoreP_defaultParams.callback;
    cfg->clockTickPeriod = ClockP_tickPeriod;
    cfg->swiIntNum = HwiP_swiPIntNum;
}

/*
 *  ======== NoRTOS_config ========
 */
void NoRTOS_setConfig(NoRTOS_Config *cfg)
{
    HwiP_disable();

    SemaphoreP_defaultParams.callback = cfg->idleCallback;
    ClockP_tickPeriod = cfg->clockTickPeriod;
    HwiP_swiPIntNum = cfg->swiIntNum;
}

/*
 *  ======== NoRTOS_start ========
 */
void NoRTOS_start(void)
{
    HwiP_enable();
}
