// Async (DMA/callback-driven) RX drain for the LR2021.
//
// Replaces the blocking steady-state poll sequence (GetAndClearIrq -> GetRxFifoLevel -> ReadRxFifo)
// with a state machine whose long SPI clocking happens via uDMA in the background:
//
//   - Thread level (ServiceRxDrain, called once per main-loop iteration) does all BUSY waiting,
//     protocol parsing, and state advancement. While a frame's DMA is in flight or the chip is
//     processing a command (BUSY high), the main loop is free to run the UAT re-arm, decoders, and
//     comms instead of spinning.
//   - SWI level (SPICallback) does the absolute minimum: raise NSS to end the frame (so the LR2021's
//     BUSY pulse overlaps main-loop time) and set the completion flags. NoRTOS SWIs are
//     non-preemptive, and the UAT RF SWI must issue CMD_PROP_SET_LEN within ~15 us of sync detect
//     (see sub_ghz_radio.cpp) -- nothing heavier may run in the SWI band.
//
// Timing budget: the LR2021's 256-byte RX FIFO holds ~2.2 ms of back-to-back 1090 traffic, and a
// full drain is at most 5 NSS frames + BUSY pulses, i.e. a handful of (now much shorter) loop
// iterations. Frame layouts mirror the synchronous implementations in lr2021_system.cpp /
// lr2021_fifo.cpp; the FIFO read collapses the opcode + payload phases into one (2 + level)-byte DMA
// transaction within a single NSS frame (the tx buffer clocks the opcode then zeros).

#include <ti/drivers/dpl/HwiP.h>

#include "hal.hh"
#include "lr2021.hh"

void LR2021::SPICallback(SPI_Handle handle, SPI_Transaction* transaction) {
    (void)handle;
    // SWI context: keep to a couple of GPIO/flag writes. No logging, no SPI calls, no parsing.
    LR2021* self = static_cast<LR2021*>(transaction->arg);
    if (self == nullptr) {
        return;
    }
    if (transaction == &self->async_txn_) {
        // Async drain frame: end the NSS frame immediately so the chip starts processing (BUSY pulse)
        // during main-loop time instead of waiting for the next ServiceRxDrain() call.
        self->SetNSS(true);
        self->async_ok_ = (transaction->status == SPI_TRANSFER_COMPLETED);
        self->async_in_flight_ = false;
        self->async_done_ = true;  // Written last: thread level reads async_done_ before async_ok_.
    } else {
        // Synchronous shim transfer (SPITransfer in lr2021_ll.cpp): the caller owns NSS framing at
        // thread level; only report completion.
        self->sync_status_ = transaction->status;
        self->sync_done_ = true;
    }
}

bool LR2021::PostAsyncFrame(const uint8_t* tx_buf, size_t len) {
    if (spi_handle_ == nullptr) {
        return false;
    }
    async_done_ = false;
    async_ok_ = false;
    async_txn_ = {
        .count = len,
        .txBuf = const_cast<uint8_t*>(tx_buf),  // nullptr clocks the driver's 0x00 default.
        .rxBuf = async_rx_buf_,
        .arg = this,
        .status = SPI_TRANSFER_QUEUED,
    };
    SetNSS(false);
    async_in_flight_ = true;
    if (!SPI_transfer(spi_handle_, &async_txn_)) {
        async_in_flight_ = false;
        SetNSS(true);
        return false;
    }
    return true;
}

void LR2021::EnterBusyWait(DrainState state) {
    busy_wait_start_ms_ = get_time_since_boot_ms();
    drain_state_ = state;
}

LR2021::DrainResult LR2021::EnterDrainError(const char* reason) {
    drain_error_str_ = reason;
    drain_state_ = DrainState::kError;
    return DrainResult::kError;
}

bool LR2021::StartRxDrain() {
    if (drain_state_ != DrainState::kIdle || spi_handle_ == nullptr || abort_requested_) {
        return false;
    }
    drain_irq_flags_ = 0;
    drain_fifo_level_ = 0;
    drain_fifo_full_ = false;
    drain_error_str_ = nullptr;
    EnterBusyWait(DrainState::kIrqCmdWait);
    return true;
}

LR2021::DrainResult LR2021::ServiceRxDrain() {
    while (true) {
        if (abort_requested_ && drain_state_ != DrainState::kIdle && drain_state_ != DrainState::kDataReady &&
            drain_state_ != DrainState::kError) {
            // The SYNC ISR handed the bus to the host mid-drain: unwind silently (expected, not an
            // error, matching WaitUntilReady's abort semantics).
            CancelAsync();
            return DrainResult::kIdle;
        }
        switch (drain_state_) {
            case DrainState::kIdle:
                return DrainResult::kIdle;
            case DrainState::kDataReady:
                return DrainResult::kDataReady;
            case DrainState::kError:
                return DrainResult::kError;

            // BUSY-wait states: post the next frame once the chip is ready.
            case DrainState::kIrqCmdWait:
            case DrainState::kIrqRspWait:
            case DrainState::kLevelCmdWait:
            case DrainState::kLevelRspWait:
            case DrainState::kFifoWait: {
                if (IsBusy()) {
                    if (get_time_since_boot_ms() - busy_wait_start_ms_ > kBusyTimeoutMs) {
                        return EnterDrainError("BUSY timeout");
                    }
                    return DrainResult::kInProgress;
                }
                bool posted = false;
                switch (drain_state_) {
                    case DrainState::kIrqCmdWait:
                        PackU16(async_tx_buf_, kOpcodeGetAndClearIrq);
                        posted = PostAsyncFrame(async_tx_buf_, 2);
                        drain_state_ = DrainState::kIrqCmd;
                        break;
                    case DrainState::kIrqRspWait:
                        posted = PostAsyncFrame(nullptr, 6);  // 2 (stat) + 4 (irq_flags).
                        drain_state_ = DrainState::kIrqRsp;
                        break;
                    case DrainState::kLevelCmdWait:
                        PackU16(async_tx_buf_, kOpcodeGetRxFifoLevel);
                        posted = PostAsyncFrame(async_tx_buf_, 2);
                        drain_state_ = DrainState::kLevelCmd;
                        break;
                    case DrainState::kLevelRspWait:
                        posted = PostAsyncFrame(nullptr, 4);  // 2 (stat) + 2 (level).
                        drain_state_ = DrainState::kLevelRsp;
                        break;
                    default:  // kFifoWait
                        // Single NSS frame: opcode at [0:1], then [2..] clocks zeros while the payload
                        // streams back (async_tx_buf_[2..] is kept zeroed).
                        PackU16(async_tx_buf_, kOpcodeReadRxFifo);
                        posted = PostAsyncFrame(async_tx_buf_, 2u + drain_fifo_level_);
                        drain_state_ = DrainState::kFifoRead;
                        break;
                }
                if (!posted) {
                    return EnterDrainError("SPI_transfer post failed");
                }
                return DrainResult::kInProgress;
            }

            // DMA-in-flight states: parse and advance on completion.
            case DrainState::kIrqCmd:
                if (!async_done_) {
                    return DrainResult::kInProgress;
                }
                if (!async_ok_) {
                    return EnterDrainError("GetAndClearIrq opcode frame failed");
                }
                ParseStat(UnpackU16(async_rx_buf_));
                EnterBusyWait(DrainState::kIrqRspWait);
                break;  // Loop: BUSY may already be low.
            case DrainState::kIrqRsp:
                if (!async_done_) {
                    return DrainResult::kInProgress;
                }
                if (!async_ok_) {
                    return EnterDrainError("GetAndClearIrq response frame failed");
                }
                ParseStat(UnpackU16(async_rx_buf_));
                if (last_stat_.command_status != CommandStatus::kDat &&
                    last_stat_.command_status != CommandStatus::kOk) {
                    return EnterDrainError("GetAndClearIrq bad command status");
                }
                drain_irq_flags_ = UnpackU32(async_rx_buf_ + 2);
                if (!(drain_irq_flags_ & HostIrqs::kIrqRxFifo)) {
                    drain_state_ = DrainState::kIdle;
                    return DrainResult::kNoData;
                }
                EnterBusyWait(DrainState::kLevelCmdWait);
                break;
            case DrainState::kLevelCmd:
                if (!async_done_) {
                    return DrainResult::kInProgress;
                }
                if (!async_ok_) {
                    return EnterDrainError("GetRxFifoLevel opcode frame failed");
                }
                ParseStat(UnpackU16(async_rx_buf_));
                EnterBusyWait(DrainState::kLevelRspWait);
                break;
            case DrainState::kLevelRsp: {
                if (!async_done_) {
                    return DrainResult::kInProgress;
                }
                if (!async_ok_) {
                    return EnterDrainError("GetRxFifoLevel response frame failed");
                }
                ParseStat(UnpackU16(async_rx_buf_));
                if (last_stat_.command_status != CommandStatus::kDat &&
                    last_stat_.command_status != CommandStatus::kOk) {
                    return EnterDrainError("GetRxFifoLevel bad command status");
                }
                uint16_t level = UnpackU16(async_rx_buf_ + 2);
                if (level == 0) {
                    // IRQ fired but the FIFO is empty (threshold crossed in both directions).
                    drain_state_ = DrainState::kIdle;
                    return DrainResult::kNoData;
                }
                // Full FIFO means the poll loop fell behind and the radio almost certainly dropped
                // frames on top of this; the consumer counts it (see ADSBee::UpdateLR2021).
                drain_fifo_full_ = (level >= kRxFifoMaxDepthBytes);
                drain_fifo_level_ = (level > kRxFifoMaxDepthBytes) ? kRxFifoMaxDepthBytes : level;
                EnterBusyWait(DrainState::kFifoWait);
                break;
            }
            case DrainState::kFifoRead:
                if (!async_done_) {
                    return DrainResult::kInProgress;
                }
                if (!async_ok_) {
                    return EnterDrainError("ReadRxFifo frame failed");
                }
                ParseStat(UnpackU16(async_rx_buf_));
                if (last_stat_.command_status != CommandStatus::kDat &&
                    last_stat_.command_status != CommandStatus::kOk) {
                    return EnterDrainError("ReadRxFifo bad command status");
                }
                drain_state_ = DrainState::kDataReady;
                return DrainResult::kDataReady;
        }
    }
}

void LR2021::FinishRxDrain() {
    if (drain_state_ == DrainState::kDataReady || drain_state_ == DrainState::kError) {
        drain_state_ = DrainState::kIdle;
    }
}

void LR2021::CancelAsync() {
    // Thread level only (SPI_transferCancel must not be called from an ISR here). If a DMA is in
    // flight, cancel it -- SPI_transferCancel invokes SPICallback with a canceled status, which clears
    // async_in_flight_. A completion racing the check is harmless: cancelling with nothing queued is a
    // no-op. The critical section keeps the flag reset atomic against a late-landing callback.
    if (spi_handle_ != nullptr && async_in_flight_) {
        SPI_transferCancel(spi_handle_);
    }
    uintptr_t key = HwiP_disable();
    async_done_ = false;
    async_ok_ = false;
    drain_state_ = DrainState::kIdle;
    HwiP_restore(key);
    SetNSS(true);  // Harmless DOUT update if the pin was tri-stated by the SYNC ISR.
}
