/*
 * Copyright (c) 2009-2020 Arm Limited
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
 * This file is derivative of CMSIS V5.6.0 system_ARMv81MML.h
 * Git SHA: b5f0603d6a584d1724d952fd8b0737458b90d62b
 */

/* This file is a copy of
 * https://gitlab.arm.com/iot/open-iot-sdk/arm-corstone-platform-bsp/-/blob/main/corstone300/Device/Include/system_SSE300MPS3.h
 */

#ifndef __SYSTEM_CORE_INIT_H__
#define __SYSTEM_CORE_INIT_H__

#include <stdint.h>

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

extern uint32_t SystemCoreClock; /*!< System Clock Frequency (Core Clock)  */
extern uint32_t PeripheralClock; /*!< Peripheral Clock Frequency */

/**
 * \brief  Initializes the system
 */
extern void SystemInit( void );

/**
 * \brief  Restores system core clock
 */
extern void SystemCoreClockUpdate( void );

/* *INDENT-OFF* */
#ifdef __cplusplus
    } /* extern "C" */
#endif
/* *INDENT-ON* */

#endif /* __SYSTEM_CORE_INIT_H__ */
