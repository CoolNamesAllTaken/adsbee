#include "pico.hh"
#include "hal.hh"

void spi_transfer_complete_callback(SPI_Handle handle, SPI_Transaction *transaction)
{
}

Pico::Init()
{
    bool ret = true;
    ret &= GPIO_setConfig(bsp.kSubGIRQPin, GPIO_CFG_OUT_OD_PU) == GPIO_STATUS_SUCCESS;

    SPI_Params spi_params = {
        .transferMode = SPI_MODE_CALLBACK,
        .transferTimeout = kSPITransactionTimeoutTicks,
        .transferCallbackFxn = spi_transfer_complete_callback,
        .mode = SPI_PERIPHERAL,
        .bitRate = 0,
        .dataSize = SPICoprocessorPacket::kSPITransactionMaxLenBytes,
        .frameFormat = SPI_POL0_PHA0,
        .custom = nullptr};
    spi_handle_ = SPI_open(bsp.kCoProSPIIndex, &spi_params);
    ret &= spi_handle_ != nullptr;
    return ret;
}

Pico::DeInit()
{
    if (spi_handle_ != nullptr)
    {
        SPI_close(spi_handle_);
        spi_handle_ = nullptr;
    }
    return true;
}