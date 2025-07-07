#include "pico.hh"
#include "hal.hh"
#include "unit_conversions.hh"

void spi_transfer_complete_callback(SPI_Handle handle, SPI_Transaction *transaction)
{
}

Pico::Pico(PicoConfig config_in) : config_(config_in)
{
    memset(spi_rx_buf_, 0x0, SPICoprocessorPacket::kSPITransactionMaxLenBytes);
    memset(spi_tx_buf_, 0x0, SPICoprocessorPacket::kSPITransactionMaxLenBytes);
}

Pico::~Pico()
{
}

bool Pico::Init()
{
    bool ret = true;
    ret &= GPIO_setConfig(bsp.kSubGIRQPin, GPIO_CFG_OUT_OD_PU) == GPIO_STATUS_SUCCESS;

    SPI_Params spi_params = {
        .transferMode = SPI_MODE_CALLBACK,
        .transferTimeout = kSPITransactionTimeoutMs * kUsPerMs * ClockP_getSystemTickPeriod(), // Convert ms to system ticks.
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

bool Pico::DeInit()
{
    if (spi_handle_ != nullptr)
    {
        SPI_close(spi_handle_);
        spi_handle_ = nullptr;
    }
    return true;
}

int Pico::SPIWriteReadBlocking(uint8_t *tx_buf, uint8_t *rx_buf, uint16_t len_bytes, bool end_transaction)
{
    int bytes_written = 0;

    spi_slave_transaction_t t;
    memset(&t, 0, sizeof(t));

    t.length = len_bytes * kBitsPerByte; // Transaction length is in bits
    t.tx_buffer = tx_buf == nullptr ? nullptr : spi_tx_buf_;
    t.rx_buffer = rx_buf == nullptr ? nullptr : spi_rx_buf_;

    if (tx_buf != nullptr)
    {
        memcpy(spi_tx_buf_, tx_buf, len_bytes);
    }

    /** Send a write packet from slave -> master via handshake. **/
    // Wait for a transaction to complete. Allow this task to block if no SPI transaction is received until max
    // delay. Currently, setting the delay here to anything other than portMAX_DELAY (which allows blocking
    // indefinitely) causes an error in spi_slave.c due to extra transactions getting stuck in the SPI peripheral queue.
    esp_err_t status = spi_slave_transmit(config_.spi_handle, &t, portMAX_DELAY /*kSPITransactionTimeoutTicks*/);

    if (status != ESP_OK)
    {
        if (status == ESP_ERR_TIMEOUT)
        {
            return ReturnCode::kErrorTimeout; // Timeouts fail silently.
        }
        CONSOLE_ERROR("SPICoprocesor::SPIWriteReadBlocking", "SPI transaction failed unexpectedly with code 0x%x.",
                      status);
        return kErrorGeneric;
    }
    bytes_written = CeilBitsToBytes(t.trans_len);
    if (rx_buf != nullptr)
    {
        memcpy(rx_buf, spi_rx_buf_, len_bytes);
    }
    last_bytes_transacted_ = bytes_written;
    return bytes_written;
}