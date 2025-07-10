#include "pico.hh"
#include "hal.hh"
#include "unit_conversions.hh"

// This low-level driver interacts with the high-level driver since it needs to do async callback stuff, which necessitates doing tasks that are normally done from a blocking implementation of the high level driver.
#include "spi_coprocessor.hh"
#include "object_dictionary.hh"

void spi_transfer_complete_callback(SPI_Handle handle, SPI_Transaction *transaction)
{
    pico_ll.SPIPostTransactionCallback();
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

bool Pico::SPIPostTransactionCallback()
{

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

    SPIEndTransaction();

    return true;
}
// int bytes_written = 0;

// spi_transaction.txBuf = (void *)tx_buf;
// spi_transaction.rxBuf = (void *)rx_buf;
// spi_transaction.count = len_bytes;

// bool success = SPI_transfer(spi_handle_, &spi_transaction);
// if (!success)
// {
//     CONSOLE_ERROR("Pico::SPIWriteReadBlocking", "SPI transfer returned false, indicating an error.");
//     return kSPITransactionErrorReturnedFalse; // Return -1 on failure.
// }
// else
// {
//     sem_wait(&spi_transaction_sem_); // Wait for the transaction to complete.
//     bytes_written = spi_transaction.count;
//     if (bytes_written != len_bytes)
//     {
//         CONSOLE_ERROR("Pico::SPIWriteReadBlocking", "SPI transaction length mismatch: expected %d, got %d.",
//                       len_bytes, bytes_written);
//         return kSPITransactionErrorLengthIncorrect; // Return -2 on length mismatch.
//     }
// }

// spi_slave_transaction_t t;
// memset(&t, 0, sizeof(t));

// t.length = len_bytes * kBitsPerByte; // Transaction length is in bits
// t.tx_buffer = tx_buf == nullptr ? nullptr : spi_tx_buf_;
// t.rx_buffer = rx_buf == nullptr ? nullptr : spi_rx_buf_;

// if (tx_buf != nullptr)
// {
//     memcpy(spi_tx_buf_, tx_buf, len_bytes);
// }

// /** Send a write packet from slave -> master via handshake. **/
// // Wait for a transaction to complete. Allow this task to block if no SPI transaction is received until max
// // delay. Currently, setting the delay here to anything other than portMAX_DELAY (which allows blocking
// // indefinitely) causes an error in spi_slave.c due to extra transactions getting stuck in the SPI peripheral queue.
// esp_err_t status = spi_slave_transmit(config_.spi_handle, &t, portMAX_DELAY /*kSPITransactionTimeoutTicks*/);

// if (status != ESP_OK)
// {
//     if (status == ESP_ERR_TIMEOUT)
//     {
//         return ReturnCode::kErrorTimeout; // Timeouts fail silently.
//     }
//     CONSOLE_ERROR("SPICoprocesor::SPIWriteReadBlocking", "SPI transaction failed unexpectedly with code 0x%x.",
//                   status);
//     return kErrorGeneric;
// }
// bytes_written = CeilBitsToBytes(t.trans_len);
// if (rx_buf != nullptr)
// {
//     memcpy(rx_buf, spi_rx_buf_, len_bytes);
// }
// last_bytes_transacted_ = bytes_written;
// return bytes_written;
// }

bool Pico::SPIWriteNonBlocking(uint8_t *tx_buf, uint16_t len_bytes)
{
    spi_transaction_.count = len_bytes;
    spi_transaction_len_bytes_ = len_bytes;
    if (tx_buf != nullptr)
    {
        memcpy(spi_transaction_.txBuf, tx_buf, len_bytes);
    }
    else
    {
        memset(spi_transaction_.txBuf, 0x00, len_bytes);
    }
    memset(spi_transaction_.rxBuf, 0x00, len_bytes);
    SPIBeginTransaction();
    return SPI_transfer(spi_handle_, &spi_transaction_);
}

void Pico::SPIResetTransaction()
{
    SPIEndTransaction();
    // Not sending a reply, don't solicit a transfer.
    SPIUseHandshakePin(false);
    // Queue up a read of the maximum packet length and let it roll based on what shows up next.
    // Sending tx_buf as nullptr means we send all 0x00's.
    SPIWriteNonBlocking(nullptr);
}