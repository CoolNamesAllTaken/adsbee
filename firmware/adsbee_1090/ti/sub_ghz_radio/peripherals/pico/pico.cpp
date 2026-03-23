#include "pico.hh"
#include "hal.hh"
#include "unit_conversions.hh"

// This low-level driver interacts with the high-level driver since it needs to do async callback stuff, which necessitates doing tasks that are normally done from a blocking implementation of the high level driver.
#include "spi_coprocessor.hh"
#include "object_dictionary.hh"
#include <cassert>
#include "ti/drivers/spi/SPICC26X2DMA.h" // Get access to partial return define.

void spi_transfer_complete_callback(SPI_Handle handle, SPI_Transaction *transaction)
{
    bool parse_message = !pico_ll.SPIIsUsingHandshakePin(); // Don't parse garbage sent by the RP2040 when it's reading our reply.
    pico_ll.SPIEndTransaction();
    if (parse_message)
    {
        pico_ll.SPIProcessTransaction(); // Parse message and reset the transaction.
    }
    else
    {
        pico_ll.SPIResetTransaction(); // Reset the transaction if we're not parsing the message.
    }
}

Pico::Pico(PicoConfig config_in) : config_(config_in)
{
    SPI_Params_init(&spi_params_);
    spi_params_.transferMode = SPI_MODE_CALLBACK;
    spi_params_.transferTimeout = SPI_WAIT_FOREVER;
    /*kSPITransactionTimeoutMs * kUsPerMs * ClockP_getSystemTickPeriod()*/ // Convert ms to system ticks.
    spi_params_.transferCallbackFxn = spi_transfer_complete_callback;
    spi_params_.mode = SPI_PERIPHERAL;
    // spi_params_.bitRate = 4'000'000; // Not used in slave mode but needs to be reasonable since it's used to set a clock.
    spi_params_.dataSize = kBitsPerByte;
    spi_params_.frameFormat = SPI_POL1_PHA1;

    memset((void *)spi_rx_buf_, 0x0, kSPITransactionMaxLenBytes);
    memset((void *)spi_tx_buf_, 0xBE, kSPITransactionMaxLenBytes);
}

Pico::~Pico()
{
}

bool Pico::Init()
{
    bool ret = true;
    // ret &= GPIO_setConfig(bsp.kSubGIRQPin, GPIO_CFG_OUT_OD_PU) == GPIO_STATUS_SUCCESS;

    spi_handle_ = SPI_open(bsp.kCoProSPIIndex, &spi_params_);
    if (spi_handle_ == nullptr)
    {
        CONSOLE_ERROR("Pico::SPIBeginTransaction", "Failed to open SPI handle.");
        return false;
    }
    SPI_control(spi_handle_, SPICC26X2DMA_RETURN_PARTIAL_ENABLE, NULL);

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

bool Pico::SPIBeginTransaction()
{
    if (use_handshake_pin_)
    {
        // Set the handshake pin high to signal the ESP32 that a transaction is ready.
        SetSPIHandshakePinLevel(true);
    }
    last_bytes_transacted_ = 0; // Reset the last bytes transacted counter.
    return true;
}

void Pico::SPIEndTransaction()
{
    SetSPIHandshakePinLevel(false); // Reset the handshake pin level to low.
}

bool Pico::SPIWriteNonBlocking(uint8_t *tx_buf, uint16_t len_bytes)
{
    spi_transaction_.count = kSPITransactionMaxLenBytes; // We want the transaction callback to be called as soon as chip select goes high. Set the max length we might see so the transaction doesn't terminate early.
    spi_transaction_len_bytes_ = len_bytes;
    spi_transaction_.status = SPI_TRANSFER_QUEUED; // Set the status to queued so that the SPI transfer can be started.
    if (tx_buf != nullptr)
    {
        // Copy contents into txBuf in case tx_buf goes out of scope and gets overwritten.
        memcpy((void *)spi_tx_buf_, (void *)tx_buf, len_bytes);
        spi_transaction_.txBuf = (void *)spi_tx_buf_;
    }
    else
    {
        spi_transaction_.txBuf = nullptr; // Use the default tx value from syscfg.
    }
    memset((void *)spi_rx_buf_, 0x0, kSPITransactionMaxLenBytes);
    spi_transaction_.rxBuf = (void *)spi_rx_buf_;

    // Tee up the callback transaction, then wiggle the handshake line, since the transfer setup takes a while.
    if (!SPI_transfer(spi_handle_, (SPI_Transaction *)&spi_transaction_))
    {
        CONSOLE_ERROR("Pico::SPIWriteNonBlocking", "Failed to queue SPI transaction.");
        return false;
    }
    SPIBeginTransaction();
    return true;
}

void Pico::SPIResetTransaction()
{
    // Not sending a reply, don't solicit a transfer.
    SPIUseHandshakePin(false);

    // Queue up a read of the maximum packet length and let it roll based on what shows up next.
    // Sending tx_buf as nullptr means we send all 0xFF's.
    SPIWriteNonBlocking(nullptr, kSPITransactionMaxLenBytes); // FIXME: Remove length.
}

bool Pico::SPIProcessTransaction()
{
    if (spi_transaction_.status != SPI_STATUS_SUCCESS && spi_transaction_.status != SPI_TRANSFER_CSN_DEASSERT)
    {
        CONSOLE_ERROR("Pico::SPIPostTransactionCallback", "SPI transaction status is not success: %d.", spi_transaction_.status);
        SPIResetTransaction();
        return false;
    }

    if (spi_transaction_.count == 0)
    {
        CONSOLE_ERROR("Pico::SPIPostTransactionCallback", "SPI transaction transferred zero bytes.");
        SPIResetTransaction();
        return false;
    }

    bool ret = true;
    uint8_t cmd = spi_rx_buf_[0];
    uint8_t *rx_buf = (uint8_t *)spi_transaction_.rxBuf;
    size_t &bytes_read = (size_t &)spi_transaction_.count;
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