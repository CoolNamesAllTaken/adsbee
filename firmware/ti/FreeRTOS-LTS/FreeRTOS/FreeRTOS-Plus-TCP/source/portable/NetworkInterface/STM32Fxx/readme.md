This is a FreeRTOS+TCP driver that works for STM32Fxx parts.


CONFIGURATION AND RUNNING
=========================

The code of stm32fxx_hal_eth.c is based on the ETH drivers as provided by ST.

These modules should be included:
- portable/NetworkInterface/STM32Fxx/NetworkInterface.c
- portable/NetworkInterface/STM32Fxx/stm32fxx_hal_eth.c

When initialising the EMAC, the driver will call the function `HAL_ETH_MspInit()`, which should do the following:

- Enable the Ethernet interface clock using:
```cpp
    __HAL_RCC_ETHMAC_CLK_ENABLE();
    __HAL_RCC_ETHMACTX_CLK_ENABLE();
    __HAL_RCC_ETHMACRX_CLK_ENABLE();
```

- Initialize the related GPIO clocks

- Configure Ethernet pin-out
    Please check the schematic of your hardware to see which pins are used.
    Also check if either MII or RMII is used ( define `ipconfigUSE_RMII`
    as 0 or 1 ).

- Configure Ethernet NVIC interrupt (IT mode)
    Choose a proper interrupt priority, defined in FreeRTOSIPConfig.h as e.g. :

```cpp
   #define ipconfigMAC_INTERRUPT_PRIORITY	( configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY )
```

The function `HAL_ETH_MspInit()` must be provided by the application. Make sure that your copy of the function is called,
and not a dummy defined as "weak".

It is assumed that one of these macros is defined at the highest level:

    STM32F1xx
    STM32F2xx
    STM32F4xx
    STM32F7xx

For instance, you can pass it to the compiler with the `-D` option:

    gcc ... -D STM32F4xx=1

And sub-models may also be indicated, such as `STM32F401xC` or `STM32F407xx`.

The driver has been tested on both Eval and Discovery boards with STM32F1, STM32F2, STM32F4 and STM32F7. The F1 and F2 boards
have only be tested by customers who reported about it on the FreeRTOS forum.

Note that it is required to define `HAL_ETH_MODULE_ENABLED` in your STM32 configuration file. The name of this file is one out
of:

    stm32f1xx_hal_conf.h
    stm32f2xx_hal_conf.h
    stm32f4xx_hal_conf.h
    stm32f7xx_hal_conf.h

This configuration file defines the HAL modules that will be used. Here are some examples of the module macros:
~~~c
#define HAL_MODULE_ENABLED
#define HAL_ETH_MODULE_ENABLED   /* <= this one is needed to get Ethernet. */
#define HAL_SRAM_MODULE_ENABLED
#define HAL_RNG_MODULE_ENABLED
#define HAL_RTC_MODULE_ENABLED
/* etc. */
~~~

Recommended settings for STM32Fxx Network Interface:


**Defined in FreeRTOSIPConfig.h**
```cpp
#define ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES   1
#define ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM        1
#define ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM        1
#define ipconfigZERO_COPY_RX_DRIVER                   1
#define ipconfigZERO_COPY_TX_DRIVER                   1
#define ipconfigUSE_LINKED_RX_MESSAGES                1
#define ipconfigSUPPORT_NETWORK_DOWN_EVENT            1
```

**Defined in stm32f4xx_hal_conf.h**
```cpp
#define ETH_RXBUFNB                                   3 or 4
#define ETH_TXBUFNB                                   1 or 2
#define ETH_RX_BUF_SIZE                               ( ipconfigNETWORK_MTU + 36 )
#define ETH_TX_BUF_SIZE                               ( ipconfigNETWORK_MTU + 36 )
```

The best size for `ETH_RXBUFNB` and `ETH_TXBUFNB` depends on the speed of the CPU. These macro's define the number of DMA buffers
for reception and for transmission. In general, if the CPU is very fast, you will need less buffers. You can obtain an estimate
empirically.

The optimal value of `ETH_RX_BUF_SIZE` and `ETH_TX_BUF_SIZE` depends on the actual value of `ipconfigNETWORK_MTU`.
When MTU is 1500, MTU+36 becomes a well-aligned buffer of 1536 bytes ( 0x600 ).
When MTU is 1200, MTU+48 will make 1248 ( 0x4E0 ), which is also well aligned.

Having well aligned buffers is important for CPU with memory cache. Often the caching system divides memory in blocks of 32 bytes.
When two buffers share the same cache buffer, you are bound to see data errors.

Without memory caching, let the size be at least a multiple of 8 ( for DMA ), and make it at least "ipconfigNETWORK_MTU + 14".

STM32F7xx only:

NetworkInterface.c will place the 2 DMA tables in a special section called 'first_data'.
In case 'BufferAllocation_1.c' is used, the network packets will also be declared in this section 'first_data'.
As long as the part has no caching, this section can be placed anywhere in RAM.
On an STM32F7 with an L1 data cache, it shall be placed in the first 64KB of RAM, which is always uncached.
The linker script must be changed for this, for instance as follows:

```assembly
   .data :
   {
     . = ALIGN(4);
     _sdata = .;        // create a global symbol at data start
+    *(.first_data)     // .first_data sections
     *(.data)           // .data sections
     *(.data*)          // .data* sections

     . = ALIGN(4);
     _edata = .;        // define a global symbol at data end
   } >RAM AT> FLASH
```

The driver contains these files:
- NetworkInterface.c
- stm32fxx_hal_eth.c
- stm32f2xx_hal_eth.h
- stm32f4xx_hal_eth.h
- stm32f7xx_hal_eth.h
- stm32fxx_hal_eth.h

These files are copied from ST's HAL library. These work both for STM32F4 and STM32F7.
Please remove or rename these files from the HAL distribution that you are using.

