/*
 *  ======== ti_drivers_config.c ========
 *  Configured TI-Drivers module definitions
 *
 *  DO NOT EDIT - This file is generated for the CC1312R1F3RGZ
 *  by the SysConfig tool.
 */

#include <stddef.h>
#include <stdint.h>

#ifndef DeviceFamily_CC13X2
#define DeviceFamily_CC13X2
#endif

#include <ti/devices/DeviceFamily.h>

#include "ti_drivers_config.h"

/*
 *  =============================== DMA ===============================
 */

#include <ti/drivers/dma/UDMACC26XX.h>
#include <ti/devices/cc13x2_cc26x2/driverlib/udma.h>
#include <ti/devices/cc13x2_cc26x2/inc/hw_memmap.h>

UDMACC26XX_Object udmaCC26XXObject;

const UDMACC26XX_HWAttrs udmaCC26XXHWAttrs = {
    .baseAddr        = UDMA0_BASE,
    .powerMngrId     = PowerCC26XX_PERIPH_UDMA,
    .intNum          = INT_DMA_ERR,
    .intPriority     = (~0)
};

const UDMACC26XX_Config UDMACC26XX_config[1] = {
    {
        .object         = &udmaCC26XXObject,
        .hwAttrs        = &udmaCC26XXHWAttrs,
    },
};

/*
 *  =============================== GPIO ===============================
 */

#include <ti/drivers/GPIO.h>
#include <ti/drivers/gpio/GPIOCC26XX.h>

/* The range of pins available on this device */
const uint_least8_t GPIO_pinLowerBound = 1;
const uint_least8_t GPIO_pinUpperBound = 30;

/*
 *  ======== gpioPinConfigs ========
 *  Array of Pin configurations
 */
GPIO_PinConfig gpioPinConfigs[31] = {
    0, /* Pin is not available on this device */
    GPIO_CFG_NO_DIR, /* DIO_1 */
    GPIO_CFG_NO_DIR, /* DIO_2 */
    GPIO_CFG_NO_DIR, /* DIO_3 */
    GPIO_CFG_NO_DIR, /* DIO_4 */
    GPIO_CFG_INPUT_INTERNAL | GPIO_CFG_IN_INT_NONE | GPIO_CFG_PULL_NONE_INTERNAL, /* SYNC_PIN */
    GPIO_CFG_OUTPUT_INTERNAL | GPIO_CFG_OUT_STR_MED | GPIO_CFG_OUT_LOW, /* SUBG_LED_PIN */
    GPIO_CFG_OUTPUT_INTERNAL | GPIO_CFG_OUT_STR_MED | GPIO_CFG_OUT_LOW, /* SUBG_BIAS_TEE_ENABLE_PIN */
    /* Owned by COPRO_SPI as POCI */
    GPIO_CFG_OUTPUT_INTERNAL | GPIO_CFG_OUT_STR_MED | GPIO_CFG_OUT_LOW, /* CONFIG_GPIO_COPRO_SPI_POCI */
    /* Owned by COPRO_SPI as PICO */
    GPIO_CFG_INPUT_INTERNAL | GPIO_CFG_IN_INT_NONE | GPIO_CFG_PULL_NONE_INTERNAL, /* CONFIG_GPIO_COPRO_SPI_PICO */
    /* Owned by COPRO_SPI as SCLK */
    GPIO_CFG_INPUT_INTERNAL | GPIO_CFG_IN_INT_NONE | GPIO_CFG_PULL_NONE_INTERNAL, /* CONFIG_GPIO_COPRO_SPI_SCLK */
    /* Owned by COPRO_SPI as CSN */
    GPIO_CFG_INPUT_INTERNAL | GPIO_CFG_IN_INT_RISING | GPIO_CFG_PULL_NONE_INTERNAL, /* CONFIG_GPIO_COPRO_SPI_CSN */
    GPIO_CFG_NO_DIR, /* DIO_12 */
    GPIO_CFG_NO_DIR, /* DIO_13 */
    GPIO_CFG_NO_DIR, /* DIO_14 */
    GPIO_CFG_NO_DIR, /* DIO_15 */
    GPIO_CFG_NO_DIR, /* DIO_16 */
    GPIO_CFG_NO_DIR, /* DIO_17 */
    GPIO_CFG_OUTPUT_INTERNAL | GPIO_CFG_OUT_STR_MED | GPIO_CFG_OUTPUT_OPEN_DRAIN_INTERNAL | GPIO_CFG_OUT_HIGH, /* SUBG_IRQ_PIN */
    GPIO_CFG_NO_DIR, /* DIO_19 */
    GPIO_CFG_NO_DIR, /* DIO_20 */
    GPIO_CFG_NO_DIR, /* DIO_21 */
    GPIO_CFG_NO_DIR, /* DIO_22 */
    GPIO_CFG_NO_DIR, /* DIO_23 */
    GPIO_CFG_NO_DIR, /* DIO_24 */
    GPIO_CFG_NO_DIR, /* DIO_25 */
    GPIO_CFG_NO_DIR, /* DIO_26 */
    GPIO_CFG_NO_DIR, /* DIO_27 */
    GPIO_CFG_NO_DIR, /* DIO_28 */
    GPIO_CFG_NO_DIR, /* DIO_29 */
    GPIO_CFG_NO_DIR, /* DIO_30 */
};

/*
 *  ======== gpioCallbackFunctions ========
 *  Array of callback function pointers
 *  Change at runtime with GPIO_setCallback()
 */
GPIO_CallbackFxn gpioCallbackFunctions[31];

/*
 *  ======== gpioUserArgs ========
 *  Array of user argument pointers
 *  Change at runtime with GPIO_setUserArg()
 *  Get values with GPIO_getUserArg()
 */
void* gpioUserArgs[31];

const uint_least8_t SUBG_LED_PIN_CONST = SUBG_LED_PIN;
const uint_least8_t SUBG_IRQ_PIN_CONST = SUBG_IRQ_PIN;
const uint_least8_t SYNC_PIN_CONST = SYNC_PIN;
const uint_least8_t SUBG_BIAS_TEE_ENABLE_PIN_CONST = SUBG_BIAS_TEE_ENABLE_PIN;
const uint_least8_t CONFIG_GPIO_COPRO_SPI_SCLK_CONST = CONFIG_GPIO_COPRO_SPI_SCLK;
const uint_least8_t CONFIG_GPIO_COPRO_SPI_POCI_CONST = CONFIG_GPIO_COPRO_SPI_POCI;
const uint_least8_t CONFIG_GPIO_COPRO_SPI_PICO_CONST = CONFIG_GPIO_COPRO_SPI_PICO;
const uint_least8_t CONFIG_GPIO_COPRO_SPI_CSN_CONST = CONFIG_GPIO_COPRO_SPI_CSN;

/*
 *  ======== GPIO_config ========
 */
const GPIO_Config GPIO_config = {
    .configs = (GPIO_PinConfig *)gpioPinConfigs,
    .callbacks = (GPIO_CallbackFxn *)gpioCallbackFunctions,
    .userArgs = gpioUserArgs,
    .intPriority = 0x80
};

/*
 *  =============================== Power ===============================
 */
#include <ti/drivers/Power.h>
#include <ti/drivers/power/PowerCC26X2.h>
#include "ti_drivers_config.h"

extern void PowerCC26XX_standbyPolicy(void);
extern bool PowerCC26XX_calibrate(unsigned int);

const PowerCC26X2_Config PowerCC26X2_config = {
    .enablePolicy             = true,
    .policyInitFxn            = NULL,
    .policyFxn                = PowerCC26XX_standbyPolicy,
    .calibrateFxn             = PowerCC26XX_calibrate,
    .calibrateRCOSC_LF        = true,
    .calibrateRCOSC_HF        = true,
    .enableTCXOFxn            = NULL
};



/*
 *  =============================== RF Driver ===============================
 */
#include <ti/drivers/GPIO.h>
#include <ti/devices/DeviceFamily.h>
#include DeviceFamily_constructPath(driverlib/ioc.h)
#include <ti/drivers/rf/RF.h>

/*
 * Platform-specific driver configuration
 */
const RFCC26XX_HWAttrsV2 RFCC26XX_hwAttrs = {
    .hwiPriority        = (~0),
    .swiPriority        = (uint8_t)0,
    .xoscHfAlwaysNeeded = true,
    .globalCallback     = NULL,
    .globalEventMask    = 0
};


/*
 *  =============================== SPI DMA ===============================
 */
#include <ti/drivers/SPI.h>
#include <ti/drivers/spi/SPICC26X2DMA.h>
#include <ti/drivers/dma/UDMACC26XX.h>

#include <ti/devices/DeviceFamily.h>
#include DeviceFamily_constructPath(driverlib/ioc.h)

#define CONFIG_SPI_COUNT 1

/*
 *  ======== spiCC26X2DMAObjects ========
 */
SPICC26X2DMA_Object spiCC26X2DMAObjects[CONFIG_SPI_COUNT];

/*
 * ======== spiCC26X2DMA uDMA Table Entries  ========
 */
        ALLOCATE_CONTROL_TABLE_ENTRY(dmaSpi0TxControlTableEntry, UDMA_CHAN_SSI0_TX);
        ALLOCATE_CONTROL_TABLE_ENTRY(dmaSpi0RxControlTableEntry, UDMA_CHAN_SSI0_RX);
        ALLOCATE_CONTROL_TABLE_ENTRY(dmaSpi0TxAltControlTableEntry, (UDMA_CHAN_SSI0_TX | UDMA_ALT_SELECT));
        ALLOCATE_CONTROL_TABLE_ENTRY(dmaSpi0RxAltControlTableEntry, (UDMA_CHAN_SSI0_RX | UDMA_ALT_SELECT));

/*
 *  ======== spiCC26X2DMAHWAttrs ========
 */
const SPICC26X2DMA_HWAttrs spiCC26X2DMAHWAttrs[CONFIG_SPI_COUNT] = {
    /* COPRO_SPI */
    {
        .baseAddr = SSI0_BASE,
        .intNum = INT_SSI0_COMB,
        .intPriority = 0xa0,
        .swiPriority = 0,
        .powerMngrId = PowerCC26XX_PERIPH_SSI0,
        .defaultTxBufValue = ~0,
        .rxChannelBitMask = 1<<UDMA_CHAN_SSI0_RX,
        .txChannelBitMask = 1<<UDMA_CHAN_SSI0_TX,
        .dmaTxTableEntryPri = &dmaSpi0TxControlTableEntry,
        .dmaRxTableEntryPri = &dmaSpi0RxControlTableEntry,
        .dmaTxTableEntryAlt = &dmaSpi0TxAltControlTableEntry,
        .dmaRxTableEntryAlt = &dmaSpi0RxAltControlTableEntry,
        .minDmaTransferSize = 10000,
        .txPinMux    = IOC_PORT_MCU_SSI0_TX,
        .rxPinMux    = IOC_PORT_MCU_SSI0_RX,
        .clkPinMux   = IOC_PORT_MCU_SSI0_CLK,
        .csnPinMux   = IOC_PORT_MCU_SSI0_FSS,
        .picoPin = CONFIG_GPIO_COPRO_SPI_PICO,
        .pociPin = CONFIG_GPIO_COPRO_SPI_POCI,
        .clkPin  = CONFIG_GPIO_COPRO_SPI_SCLK,
        .csnPin  = CONFIG_GPIO_COPRO_SPI_CSN
    },
};

/*
 *  ======== SPI_config ========
 */
const SPI_Config SPI_config[CONFIG_SPI_COUNT] = {
    /* COPRO_SPI */
    {
        .fxnTablePtr = &SPICC26X2DMA_fxnTable,
        .object = &spiCC26X2DMAObjects[COPRO_SPI],
        .hwAttrs = &spiCC26X2DMAHWAttrs[COPRO_SPI]
    },
};

const uint_least8_t COPRO_SPI_CONST = COPRO_SPI;
const uint_least8_t SPI_count = CONFIG_SPI_COUNT;

#include <ti/drivers/Board.h>

/*
 *  ======== Board_initHook ========
 *  Perform any board-specific initialization needed at startup.  This
 *  function is declared weak to allow applications to override it if needed.
 */
void __attribute__((weak)) Board_initHook(void)
{
}

/*
 *  ======== Board_init ========
 *  Perform any initialization needed before using any board APIs
 */
void Board_init(void)
{
    /* ==== /ti/drivers/Power initialization ==== */
    Power_init();

    /* ==== /ti/devices/CCFG initialization ==== */

    /* ==== /ti/drivers/GPIO initialization ==== */
    /* Setup GPIO module and default-initialise pins */
    GPIO_init();

    /* ==== /ti/drivers/RF initialization ==== */


    Board_initHook();
}

