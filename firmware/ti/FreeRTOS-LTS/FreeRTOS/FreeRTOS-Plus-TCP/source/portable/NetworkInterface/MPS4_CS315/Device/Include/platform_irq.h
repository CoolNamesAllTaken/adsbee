/*
 * Copyright (c) 2024 Arm Limited. All rights reserved.
 *
 * Licensed under the Apache License Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing software
 * distributed under the License is distributed on an "AS IS" BASIS
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef __PLATFORM_IRQ_H__
#define __PLATFORM_IRQ_H__

typedef enum _IRQn_Type
{
    NonMaskableInt_IRQn = -14,          /* Non Maskable Interrupt */
    HardFault_IRQn = -13,               /* HardFault Interrupt */
    MemoryManagement_IRQn = -12,        /* Memory Management Interrupt */
    BusFault_IRQn = -11,                /* Bus Fault Interrupt */
    UsageFault_IRQn = -10,              /* Usage Fault Interrupt */
    SecureFault_IRQn = -9,              /* Secure Fault Interrupt */
    SVCall_IRQn = -5,                   /* SV Call Interrupt */
    DebugMonitor_IRQn = -4,             /* Debug Monitor Interrupt */
    PendSV_IRQn = -2,                   /* Pend SV Interrupt */
    SysTick_IRQn = -1,                  /* System Tick Interrupt */
    NONSEC_WATCHDOG_RESET_REQ_IRQn = 0, /* Non-Secure Watchdog Reset
                                         * Request Interrupt
                                         */
    NONSEC_WATCHDOG_IRQn = 1,           /* Non-Secure Watchdog Interrupt */
    SLOWCLK_TIMER_IRQn = 2,             /* SLOWCLK Timer Interrupt */
    TIMER0_IRQn = 3,                    /* TIMER 0 Interrupt */
    TIMER1_IRQn = 4,                    /* TIMER 1 Interrupt */
    TIMER2_IRQn = 5,                    /* TIMER 2 Interrupt */
    /* Reserved                        = 6,       Reserved */
    /* Reserved                        = 7,       Reserved */
    /* Reserved                        = 8,       Reserved */
    MPC_IRQn = 9,           /* MPC Combined (Secure) Interrupt */
    PPC_IRQn = 10,          /* PPC Combined (Secure) Interrupt */
    MSC_IRQn = 11,          /* MSC Combined (Secure) Interrput */
    BRIDGE_ERROR_IRQn = 12, /* Bridge Error Combined
                             * (Secure) Interrupt
                             */
    /* Reserved                        = 13,      Reserved */
    Combined_PPU_IRQn = 14, /* Combined PPU */
    SDC_IRQn = 15,          /* Secure Debug channel Interrupt */
    NPU0_IRQn = 16,         /* NPU0 */
    /* Reserved                        = 17,      Reserved */
    /* Reserved                        = 18,      Reserved */
    /* Reserved                        = 19,      Reserved */
    KMU_IRQn = 20, /* KMU Interrupt */
    /* Reserved                        = 21,      Reserved */
    /* Reserved                        = 22,      Reserved */
    /* Reserved                        = 23,      Reserved */
    DMA_SEC_Combined_IRQn = 24,            /* DMA Secure Combined Interrupt */
    DMA_NONSEC_Combined_IRQn = 25,         /* DMA Non-Secure Combined Interrupt */
    DMA_SECURITY_VIOLATION_IRQn = 26,      /* DMA Security Violation Interrupt */
    TIMER3_AON_IRQn = 27,                  /* TIMER 3 AON Interrupt */
    CPU0_CTI_0_IRQn = 28,                  /* CPU0 CTI IRQ 0 */
    CPU0_CTI_1_IRQn = 29,                  /* CPU0 CTI IRQ 1 */
    SAM_CRITICAL_SEVERITY_FAULT_IRQn = 30, /* SAM Critical Severity Fault Interrupt */
    SAM_SEVERITY_FAULT_HANDLER_IRQn = 31,  /* SAM Severity Fault Handler Interrupt */
    /* Reserved                        = 32,      Reserved */
    UARTRX0_IRQn = 33,                     /* UART 0 RX Interrupt */
    UARTTX0_IRQn = 34,                     /* UART 0 TX Interrupt */
    UARTRX1_IRQn = 35,                     /* UART 1 RX Interrupt */
    UARTTX1_IRQn = 36,                     /* UART 1 TX Interrupt */
    UARTRX2_IRQn = 37,                     /* UART 2 RX Interrupt */
    UARTTX2_IRQn = 38,                     /* UART 2 TX Interrupt */
    UARTRX3_IRQn = 39,                     /* UART 3 RX Interrupt */
    UARTTX3_IRQn = 40,                     /* UART 3 TX Interrupt */
    UARTRX4_IRQn = 41,                     /* UART 4 RX Interrupt */
    UARTTX4_IRQn = 42,                     /* UART 4 TX Interrupt */
    UART0_Combined_IRQn = 43,              /* UART 0 Combined Interrupt */
    UART1_Combined_IRQn = 44,              /* UART 1 Combined Interrupt */
    UART2_Combined_IRQn = 45,              /* UART 2 Combined Interrupt */
    UART3_Combined_IRQn = 46,              /* UART 3 Combined Interrupt */
    UART4_Combined_IRQn = 47,              /* UART 4 Combined Interrupt */
    UARTOVF_IRQn = 48,                     /* UART 0, 1, 2, 3, 4 & 5 Overflow Interrupt */
    ETHERNET_IRQn = 49,                    /* Ethernet Interrupt */
    I2S_IRQn = 50,                         /* Audio I2S Interrupt */
    /* Reserved                        = 51,      Reserved */
    /* Reserved                        = 52,      Reserved */
    /* Reserved                        = 53,      Reserved */
    /* Reserved                        = 54,      Reserved */
    /* Reserved                        = 55,      Reserved */
    /* Reserved                        = 56,      Reserved */
    DMA_CHANNEL_0_IRQn = 57,  /* DMA Channel 0 Interrupt */
    DMA_CHANNEL_1_IRQn = 58,  /* DMA Channel 1 Interrupt */
    /* Reserved                        = 59:68    Reserved */
    GPIO0_Combined_IRQn = 69, /* GPIO 0 Combined Interrupt */
    GPIO1_Combined_IRQn = 70, /* GPIO 1 Combined Interrupt */
    GPIO2_Combined_IRQn = 71, /* GPIO 2 Combined Interrupt */
    GPIO3_Combined_IRQn = 72, /* GPIO 3 Combined Interrupt */
    /* Reserved                        = 73:124   Reserved */
    UARTRX5_IRQn = 125,       /* UART 5 RX Interrupt */
    UARTTX5_IRQn = 126,       /* UART 5 TX Interrupt */
    /* Reserved                        = 127       Reserved */
    RTC_IRQn = 128,           /* RTC Interrupt */
    /* Reserved                        = 129:131   Reserved */
    ISP_IRQn = 132,           /* ISP C55 Interrupt */
    HDLCD_IRQn = 133,         /* HDLCD Interrupt */
    /* Reserved                        = 134:223   Reserved */
    ARM_VSI0_IRQn = 224,      /* VSI 0 Interrupt */
    ARM_VSI1_IRQn = 225,      /* VSI 1 Interrupt */
    ARM_VSI2_IRQn = 226,      /* VSI 2 Interrupt */
    ARM_VSI3_IRQn = 227,      /* VSI 3 Interrupt */
    ARM_VSI4_IRQn = 228,      /* VSI 4 Interrupt */
    ARM_VSI5_IRQn = 229,      /* VSI 5 Interrupt */
    ARM_VSI6_IRQn = 230,      /* VSI 6 Interrupt */
    ARM_VSI7_IRQn = 231,      /* VSI 7 Interrupt */
} IRQn_Type;

#endif /* __PLATFORM_IRQ_H__ */
