#include "pico.hh"
#include "hal.hh"
#include "unit_conversions.hh"

// This low-level driver interacts with the high-level driver since it needs to do async callback stuff, which necessitates doing tasks that are normally done from a blocking implementation of the high level driver.
#include "spi_coprocessor.hh"
#include "object_dictionary.hh"
#include <cassert>

unsigned char spi_tx_buf_[Pico::kSPITransactionMaxLenBytes];
unsigned char spi_rx_buf_[Pico::kSPITransactionMaxLenBytes];
SPI_Transaction spi_transaction_ = {
    .count = Pico::kSPITransactionMaxLenBytes,
    .txBuf = (void *)spi_tx_buf_,
    .rxBuf = (void *)spi_rx_buf_,
    .arg = nullptr};

void spi_transfer_complete_callback(SPI_Handle handle, SPI_Transaction *transaction)
{
    ((Pico *)(transaction->arg))->SPIPostTransactionCallback(handle, transaction);
}

Pico::Pico(PicoConfig config_in) : config_(config_in)
{
    // spi_rx_buf_ = (uint8_t *)malloc(100); // SPICoprocessorPacket::kSPITransactionMaxLenBytes);
    // spi_tx_buf_ = (uint8_t *)malloc(100); // SPICoprocessorPacket::kSPITransactionMaxLenBytes);
    // assert(spi_rx_buf_ != nullptr);
    // assert(spi_tx_buf_ != nullptr);

    memset((void *)spi_rx_buf_, 0x0, kSPITransactionMaxLenBytes);
    memset((void *)spi_tx_buf_, 0xBE, kSPITransactionMaxLenBytes);
}

Pico::~Pico()
{
    // free(spi_rx_buf_);
    // free(spi_tx_buf_);
}

bool Pico::Init()
{
    bool ret = true;
    ret &= GPIO_setConfig(bsp.kSubGIRQPin, GPIO_CFG_OUT_OD_PU) == GPIO_STATUS_SUCCESS;

    // SPI_init is called during peripheral initialization before this function is invoked.
    SPI_Params spi_params;
    SPI_Params_init(&spi_params); // Fill spi_params with default settings.
    // spi_params.transferMode = SPI_MODE_CALLBACK; // was commented before Caitlin
    spi_params.transferMode = SPI_MODE_BLOCKING;                           // SPI_MODE_CALLBACK; // was commented before Caitlin
    spi_params.transferTimeout = SPI_WAIT_FOREVER;                         // was commented before Caitlin
    /*kSPITransactionTimeoutMs * kUsPerMs * ClockP_getSystemTickPeriod()*/ // Convert ms to system ticks.
    // spi_params.transferCallbackFxn = spi_transfer_complete_callback;       // was commented before Caitlin
    spi_params.mode = SPI_PERIPHERAL;
    spi_params.bitRate = 4'000'000; // Not used in slave mode but needs to be reasonable since it's used to set a clock.
    spi_params.dataSize = kBitsPerByte;
    spi_params.frameFormat = SPI_POL0_PHA0;
    spi_handle_ = SPI_open(bsp.kCoProSPIIndex, &spi_params);

    ret &= spi_handle_ != nullptr;

    // Start the callback chain by kicking off the first transaction.
    SPIResetTransaction();
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

bool Pico::Update()
{
    bool ret = true;
    if (spi_transaction_.status != SPI_TRANSFER_QUEUED)
    {
        ret &= SPIProcessTransaction();
    }
    UpdateNetworkLED();
    return ret;
}

void Pico::SPIPostTransactionCallback(SPI_Handle spi_handle, SPI_Transaction *transaction)
{
    SPIEndTransaction();
}

bool Pico::SPIWriteNonBlocking(uint8_t *tx_buf, uint16_t len_bytes)
{
    spi_transaction_.count = len_bytes;
    spi_transaction_len_bytes_ = len_bytes;
    spi_transaction_.txBuf = (void *)tx_buf;
    spi_transaction_.rxBuf = (void *)spi_rx_buf_;
    // spi_transaction_.txBuf = nullptr;
    // spi_transaction_.rxBuf = nullptr;
    // spi_transaction_.arg = this;
    // if (tx_buf != nullptr)
    // {
    //     memcpy(spi_transaction_.txBuf, tx_buf, len_bytes);
    // }
    // else
    // {
    //     memset(spi_transaction_.txBuf, 0xBE, len_bytes);
    // }
    // memset(spi_transaction_.rxBuf, 0x00, len_bytes);
    SPIBeginTransaction();
    return SPI_transfer(spi_handle_, &spi_transaction_);
}

void Pico::SPIResetTransaction()
{
    // Not sending a reply, don't solicit a transfer.
    SPIUseHandshakePin(false);
    // Queue up a read of the maximum packet length and let it roll based on what shows up next.
    // Sending tx_buf as nullptr means we send all 0x00's.
    SPIWriteNonBlocking(spi_tx_buf_, 10); // FIXME: Remove length.
}

bool Pico::SPIProcessTransaction()
{
    SPIResetTransaction();
    return true;
    // End test

    if (spi_transaction_.status != SPI_STATUS_SUCCESS)
    {
        CONSOLE_ERROR("Pico::SPIPostTransactionCallback", "SPI transaction status is not success: %d.", spi_transaction_.status);
        SPIResetTransaction();
        return false;
    }
    if (spi_transaction_.count != spi_transaction_len_bytes_)
    {
        CONSOLE_ERROR("Pico::SPIPostTransactionCallback", "SPI transaction length mismatch: expected %d, got %d.",
                      spi_transaction_len_bytes_, spi_transaction_.count);
        SPIResetTransaction();
        return false;
    }
    if (spi_transaction_.count == 0)
    {
        CONSOLE_ERROR("Pico::SPIPostTransactionCallback", "SPI transaction transferred zero bytes..");
        SPIResetTransaction();
        return false;
    }

    bool ret = true;
    uint8_t cmd = spi_rx_buf_[0];
    uint8_t *rx_buf = (uint8_t *)spi_transaction_.rxBuf;
    size_t &bytes_read = spi_transaction_.count;
    switch (cmd)
    {
    case ObjectDictionary::SCCommand::kCmdWriteToSlave:
    case ObjectDictionary::SCCommand::kCmdWriteToSlaveRequireAck:
    {
        SPICoprocessorPacket::SCWritePacket write_packet = SPICoprocessorPacket::SCWritePacket(rx_buf, bytes_read);
        if (!write_packet.IsValid())
        {
            CONSOLE_ERROR("Pico::SPIPostTransactionCallback",
                          "Received unsolicited write to slave with bad checksum, packet length %d Bytes.",
                          bytes_read);
            SPIResetTransaction();
            return false;
        }
        ret =
            object_dictionary.SetBytes(write_packet.addr, write_packet.data, write_packet.len, write_packet.offset);
        bool ack = true;
        if (!ret)
        {
            CONSOLE_ERROR("Pico::SPIPostTransactionCallback",
                          "Failed to write data for %d Byte write to slave at address 0x%x with offset %d Bytes.",
                          write_packet.len, write_packet.addr, write_packet.offset);
            ack = false;
        }
        if (cmd == ObjectDictionary::SCCommand::kCmdWriteToSlaveRequireAck)
        {
            pico.SPISendAck(ack);
        }
        break;
    }
    case ObjectDictionary::SCCommand::kCmdReadFromSlave:
    {
        SPICoprocessorPacket::SPICoprocessorPacket::SCReadRequestPacket read_request_packet =
            SPICoprocessorPacket::SCReadRequestPacket(rx_buf, bytes_read);
        if (!read_request_packet.IsValid())
        {
            CONSOLE_ERROR("Pico::SPIPostTransactionCallback",
                          "Received unsolicited read from slave with bad checksum, packet length %d Bytes.",
                          bytes_read);
            SPIResetTransaction();
            return false;
        }

        SPICoprocessorPacket::SCResponsePacket response_packet;
        response_packet.cmd = ObjectDictionary::SCCommand::kCmdDataBlock;
        ret = object_dictionary.GetBytes(read_request_packet.addr, response_packet.data, read_request_packet.len,
                                         read_request_packet.offset);
        if (!ret)
        {
            CONSOLE_ERROR("Pico::SPIPostTransactionCallback",
                          "Failed to retrieve data for %d Byte read from slave at address 0x%x",
                          read_request_packet.len, read_request_packet.addr);
            SPIResetTransaction();
            return false;
        }
        response_packet.data_len_bytes = read_request_packet.len; // Assume the correct number of bytes were read.
        response_packet.PopulateCRC();
        SPIUseHandshakePin(true); // Solicit a read from the RP2040.
        SPIWriteNonBlocking(response_packet.GetBuf(), response_packet.GetBufLenBytes());
        break;
    }
    default:
        CONSOLE_ERROR("Pico::SPIPostTransactionCallback",
                      "Received unsolicited packet from RP2040 with unsupported cmd=%d, packet length %d Bytes.",
                      cmd, bytes_read);
        SPIResetTransaction();
        return false;
    }

    return true;
}