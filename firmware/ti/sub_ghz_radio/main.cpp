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

extern void app_main(void);

void exception_handler()
{
    while (1)
    {
    }
}

/*
 *  ======== main ========
 */
extern "C" int main(void)
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

    static const uint16_t kNumBlinks = 5;
    for (uint16_t i = 0; i < kNumBlinks; ++i)
    {
        GPIO_write(bsp.kSubGLEDPin, 1);
        usleep(50000); // 50ms
        GPIO_write(bsp.kSubGLEDPin, 0);
        usleep(50000); // 50ms
    }

    // unsigned char spi_rx_buf[Pico::kSPITransactionMaxLenBytes] = {0};
    // unsigned char spi_tx_buf[Pico::kSPITransactionMaxLenBytes] = {0};
    // memset((void *)spi_tx_buf, 0xBE, Pico::kSPITransactionMaxLenBytes);
    // SPI_Transaction spi_transaction = {
    //     .count = Pico::kSPITransactionMaxLenBytes,
    //     .txBuf = (void *)spi_tx_buf,
    //     .rxBuf = (void *)spi_rx_buf,
    //     .arg = nullptr};
    // SPI_Params spi_params;
    // SPI_Params_init(&spi_params);
    // spi_params.transferMode = SPI_MODE_BLOCKING; // SPI_MODE_CALLBACK; // was commented

    // spi_params.transferTimeout = SPI_WAIT_FOREVER; // was commented before Caitlin
    // spi_params.mode = SPI_PERIPHERAL;
    // spi_params.bitRate = 4'000'000; // Not used in slave mode but needs to be reasonable since it's used to set a clock.
    // spi_params.dataSize = kBitsPerByte;
    // spi_params.frameFormat = SPI_POL1_PHA1;

    // SPI_Handle spi_handle = SPI_open(bsp.kCoProSPIIndex, &spi_params);
    // while (true)
    // {
    //     SPI_transfer(spi_handle, &spi_transaction);
    //     // usleep(50000); // 50ms
    //     GPIO_toggle(bsp.kSubGLEDPin);
    // }

    // Initialize the SPI coprocessor.
    if (!pico.Init())
    {
        CONSOLE_ERROR("main", "Failed to initialize SPI coprocessor.");
        exception_handler();
    }

    while (true)
    {
        pico.Update();
        GPIO_write(bsp.kSubGLEDPin, 1);
        usleep(50000); // 50ms
        GPIO_write(bsp.kSubGLEDPin, 0);
        usleep(50000); // 50ms
    }

    // app_main();
}

void app_main()
{
}
