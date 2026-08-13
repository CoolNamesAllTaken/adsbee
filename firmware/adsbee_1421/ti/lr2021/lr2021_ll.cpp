// Low level functions for LR2021 driver.

#include "comms.hh"
#include "lr2021.hh"

bool LR2021::SPITransfer(const uint8_t* tx_buf, uint8_t* rx_buf, size_t length) {
    if (spi_handle_ == nullptr) {
        CONSOLE_ERROR("LR2021::SPITransfer", "SPI handle is null; did you forget to call Init()?");
        return false;
    }
    SPI_Transaction txn = {
        .count = length,
        .txBuf = const_cast<uint8_t*>(tx_buf),
        .rxBuf = rx_buf,
        .arg = nullptr,  // Argument to be passed to the callback function.
        .status = SPI_TRANSFER_QUEUED,
    };

    // The LPF2 SPI driver accepts nullptr for txBuf (sends 0x00) and for
    // rxBuf (discards incoming bytes), matching the LR2021HAL contract.

    return SPI_transfer(spi_handle_, &txn);
}

void LR2021::SetNSS(bool high) { GPIO_write(config_.gpio_nss, high ? 1 : 0); }

bool LR2021::IsBusy() { return GPIO_read(config_.gpio_busy) != 0; }

void LR2021::SetEnable(bool enabled) { GPIO_write(config_.gpio_enable, enabled ? 1 : 0); }