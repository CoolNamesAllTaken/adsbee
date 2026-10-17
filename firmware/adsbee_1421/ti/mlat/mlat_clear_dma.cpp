#include "mlat_clear_dma.hh"

#include <ti/devices/DeviceFamily.h>
#include DeviceFamily_constructPath(driverlib/timer.h)
#include DeviceFamily_constructPath(driverlib/udma.h)
#include DeviceFamily_constructPath(inc/hw_event.h)
#include DeviceFamily_constructPath(inc/hw_gpio.h)
#include DeviceFamily_constructPath(inc/hw_gpt.h)
#include DeviceFamily_constructPath(inc/hw_memmap.h)
#include DeviceFamily_constructPath(inc/hw_spi.h)
#include DeviceFamily_constructPath(inc/hw_types.h)
#include <ti/drivers/dma/UDMACC26XX.h>
#include <ti/drivers/dpl/HwiP.h>

#include "cycle_counter.hh"
#include "mlat_capture.hh"
#include "ti_drivers_config.h"

// Channel 10 (GPT0B): the clear. Channel 11 (GPT1A, software requests only): the end of the frame. The linker
// script places these control structures in the driver's control table.
ALLOCATE_CONTROL_TABLE_ENTRY(dmaGPT0BPriControlTableEntry, (UDMA_CHAN_TIMER0_B + UDMA_PRI_SELECT));
ALLOCATE_CONTROL_TABLE_ENTRY(dmaGPT0BAltControlTableEntry, (UDMA_CHAN_TIMER0_B + UDMA_ALT_SELECT));
ALLOCATE_CONTROL_TABLE_ENTRY(dmaGPT1APriControlTableEntry, (UDMA_CHAN_TIMER1_A + UDMA_PRI_SELECT));
ALLOCATE_CONTROL_TABLE_ENTRY(dmaGPT1AAltControlTableEntry, (UDMA_CHAN_TIMER1_A + UDMA_ALT_SELECT));

namespace mlat_clear_dma {

static constexpr uint32_t kChClear = UDMA_CHAN_TIMER0_B;
static constexpr uint32_t kChEnd = UDMA_CHAN_TIMER1_A;
static constexpr uint32_t kClearBytes = 6;
static constexpr uint32_t kWaitMaxUs = 30;  // A chain takes 15 to 20 us.

// Words the lists copy into registers, in SRAM. Set/clear registers ignore zero bits.
static uint32_t kNssMask = 1u << LR_CS;
static uint32_t kClearBit = 1u << kChClear;
static uint32_t kEndBit = 1u << kChEnd;
static uint32_t kOne = 1;
static uint32_t kZero = 0;
static uint32_t clear_control = 0;  // Channel 10 primary control word when armed.
static uint32_t end_control = 0;    // Channel 11 primary control word when armed.

static volatile uint32_t chain_busy = 0;  // 1 from the third task of the clear list to the last task of the end list.
static volatile uint8_t rx_sink[kClearBytes];

static bool running = false;
static bool armed = false;
static Counters counters_;

#define TASK(count, size, src_inc, src, dst_inc, dst, arb, mode)                                                    \
    uDMATaskStructEntry(count, size, src_inc, const_cast<void*>(reinterpret_cast<const volatile void*>(src)), dst_inc, \
                        const_cast<void*>(reinterpret_cast<const volatile void*>(dst)), arb, mode)

static tDMAControlTable clear_list[7];
static tDMAControlTable end_list[6];

static void BuildLists(const uint8_t* clear_cmd) {
    const uint32_t mem = UDMA_MODE_MEM_SCATTER_GATHER;
    void* const doutclr = reinterpret_cast<void*>(GPIO_BASE + GPIO_O_DOUTCLR31_0);
    void* const doutset = reinterpret_cast<void*>(GPIO_BASE + GPIO_O_DOUTSET31_0);
    void* const txdata = reinterpret_cast<void*>(SPI0_BASE + SPI_O_TXDATA);
    void* const rxdata = reinterpret_cast<void*>(SPI0_BASE + SPI_O_RXDATA);
    void* const enaset = reinterpret_cast<void*>(UDMA0_BASE + UDMA_O_SETCHANNELEN);
    void* const prialt_clr = reinterpret_cast<void*>(UDMA0_BASE + UDMA_O_CLEARCHNLPRIALT);
    void* const softreq = reinterpret_cast<void*>(UDMA0_BASE + UDMA_O_SOFTREQ);
    // A list cannot re-arm itself, so each list re-arms the other. NSS low and the bytes go first; the 48 bits take
    // 4 us to shift out, which the tasks after them cover (about 1.4 us each, measured) before the end list raises
    // NSS. The RX FIFO is emptied after NSS rises: only the next chain or the next driver transfer needs it empty.
    const tDMAControlTable clear[] = {
        TASK(1, UDMA_SIZE_32, UDMA_SRC_INC_NONE, &kNssMask, UDMA_DST_INC_NONE, doutclr, UDMA_ARB_1, mem),
        TASK(kClearBytes, UDMA_SIZE_8, UDMA_SRC_INC_8, clear_cmd, UDMA_DST_INC_NONE, txdata, UDMA_ARB_8, mem),
        TASK(1, UDMA_SIZE_32, UDMA_SRC_INC_NONE, &kOne, UDMA_DST_INC_NONE, &chain_busy, UDMA_ARB_1, mem),
        TASK(1, UDMA_SIZE_32, UDMA_SRC_INC_NONE, &end_control, UDMA_DST_INC_NONE,
             &dmaGPT1APriControlTableEntry.ui32Control, UDMA_ARB_1, mem),
        TASK(1, UDMA_SIZE_32, UDMA_SRC_INC_NONE, &kEndBit, UDMA_DST_INC_NONE, prialt_clr, UDMA_ARB_1, mem),
        TASK(1, UDMA_SIZE_32, UDMA_SRC_INC_NONE, &kEndBit, UDMA_DST_INC_NONE, enaset, UDMA_ARB_1, mem),
        TASK(1, UDMA_SIZE_32, UDMA_SRC_INC_NONE, &kEndBit, UDMA_DST_INC_NONE, softreq, UDMA_ARB_1, UDMA_MODE_AUTO),
    };
    const tDMAControlTable end[] = {
        TASK(1, UDMA_SIZE_32, UDMA_SRC_INC_NONE, &kNssMask, UDMA_DST_INC_NONE, doutset, UDMA_ARB_1, mem),
        TASK(kClearBytes, UDMA_SIZE_8, UDMA_SRC_INC_NONE, rxdata, UDMA_DST_INC_8, rx_sink, UDMA_ARB_8, mem),
        TASK(1, UDMA_SIZE_32, UDMA_SRC_INC_NONE, &clear_control, UDMA_DST_INC_NONE,
             &dmaGPT0BPriControlTableEntry.ui32Control, UDMA_ARB_1, mem),
        TASK(1, UDMA_SIZE_32, UDMA_SRC_INC_NONE, &kClearBit, UDMA_DST_INC_NONE, prialt_clr, UDMA_ARB_1, mem),
        TASK(1, UDMA_SIZE_32, UDMA_SRC_INC_NONE, &kClearBit, UDMA_DST_INC_NONE, enaset, UDMA_ARB_1, mem),
        TASK(1, UDMA_SIZE_32, UDMA_SRC_INC_NONE, &kZero, UDMA_DST_INC_NONE, &chain_busy, UDMA_ARB_1, UDMA_MODE_AUTO),
    };
    constexpr uint32_t num_clear = sizeof(clear) / sizeof(clear[0]);
    constexpr uint32_t num_end = sizeof(end) / sizeof(end[0]);
    static_assert(num_clear == sizeof(clear_list) / sizeof(clear_list[0]) &&
                      num_end == sizeof(end_list) / sizeof(end_list[0]),
                  "task lists");
    for (uint32_t i = 0; i < num_clear; i++) clear_list[i] = clear[i];
    for (uint32_t i = 0; i < num_end; i++) end_list[i] = end[i];

    dmaGPT0BPriControlTableEntry.pvSrcEndAddr = &clear_list[num_clear - 1].ui32Spare;
    dmaGPT0BPriControlTableEntry.pvDstEndAddr = &dmaGPT0BAltControlTableEntry.ui32Spare;
    clear_control = UDMA_DST_INC_32 | UDMA_SRC_INC_32 | UDMA_SIZE_32 | UDMA_ARB_4 |
                    ((num_clear * 4 - 1) << UDMA_XFER_SIZE_S) | UDMA_MODE_MEM_SCATTER_GATHER;
    dmaGPT0BPriControlTableEntry.ui32Control = clear_control;

    dmaGPT1APriControlTableEntry.pvSrcEndAddr = &end_list[num_end - 1].ui32Spare;
    dmaGPT1APriControlTableEntry.pvDstEndAddr = &dmaGPT1AAltControlTableEntry.ui32Spare;
    end_control = UDMA_DST_INC_32 | UDMA_SRC_INC_32 | UDMA_SIZE_32 | UDMA_ARB_4 |
                  ((num_end * 4 - 1) << UDMA_XFER_SIZE_S) | UDMA_MODE_MEM_SCATTER_GATHER;
    dmaGPT1APriControlTableEntry.ui32Control = 0;  // Armed by the clear list.
}

static void ChannelReset(uint32_t ch) {
    uDMAChannelDisable(UDMA0_BASE, ch);
    HWREG(UDMA0_BASE + UDMA_O_CLEARCHNLPRIALT) = 1u << ch;
    uDMAChannelAttributeDisable(UDMA0_BASE, ch,
                                UDMA_ATTR_USEBURST | UDMA_ATTR_ALTSELECT | UDMA_ATTR_REQMASK | UDMA_ATTR_HIGH_PRIORITY);
}

void Start(const uint8_t* clear_cmd) {
    if (running || !mlat_capture::Running()) {
        return;
    }
    ChannelReset(kChClear);
    ChannelReset(kChEnd);
    uDMAChannelAttributeEnable(UDMA0_BASE, kChClear, UDMA_ATTR_REQMASK);  // Masked until Arm().
    BuildLists(clear_cmd);
    HWREG(EVENT_BASE + EVENT_O_UDMACH10SSEL) = EVENT_UDMACH10SSEL_EV_GPT0B_DMABREQ;
    HWREG(EVENT_BASE + EVENT_O_UDMACH10BSEL) = EVENT_UDMACH10BSEL_EV_GPT0B_DMABREQ;
    HWREG(EVENT_BASE + EVENT_O_UDMACH11SSEL) = EVENT_UDMACH11SSEL_EV_NONE;
    HWREG(EVENT_BASE + EVENT_O_UDMACH11BSEL) = EVENT_UDMACH11BSEL_EV_NONE;
    chain_busy = 0;
    uDMAChannelEnable(UDMA0_BASE, kChClear);

    // GPT0B: second capture of the DIO5 port event, as the trigger.
    HWREG(EVENT_BASE + EVENT_O_GPT0BCAPTSEL) = EVENT_GPT0BCAPTSEL_EV_PORT_EVENT0;
    TimerPrescaleSet(GPT0_BASE, TIMER_B, 0xFF);
    TimerLoadSet(GPT0_BASE, TIMER_B, 0xFFFF);
    TimerEventControl(GPT0_BASE, TIMER_B, TIMER_EVENT_POS_EDGE);
    HWREG(GPT0_BASE + GPT_O_DMAEV) |= GPT_DMAEV_CBEDMAEN;
    TimerEnable(GPT0_BASE, TIMER_B);
    armed = false;
    running = true;
}

void Stop() {
    if (!running) {
        return;
    }
    Disarm();
    running = false;
    HWREG(GPT0_BASE + GPT_O_DMAEV) &= ~GPT_DMAEV_CBEDMAEN;
    TimerDisable(GPT0_BASE, TIMER_B);
    uDMAChannelDisable(UDMA0_BASE, kChClear);
    uDMAChannelDisable(UDMA0_BASE, kChEnd);
}

bool Running() { return running; }
bool Armed() { return armed; }

// The clear list has started (its primary control word counts down) or the end list has not finished.
static bool ChainActive() { return chain_busy != 0 || dmaGPT0BPriControlTableEntry.ui32Control != clear_control; }

// The SPI driver keeps SPI0 enabled while idle, with its RX DMA off: bytes a chain left behind would shift the next
// transfer.
static void FlushRx() {
    while (!(HWREG(SPI0_BASE + SPI_O_STAT) & SPI_STAT_RFE)) {
        (void)HWREG(SPI0_BASE + SPI_O_RXDATA);
    }
}

static bool SpiIdle() {
    return (HWREG(SPI0_BASE + SPI_O_CTL1) & SPI_CTL1_ENABLE) && !(HWREG(SPI0_BASE + SPI_O_STAT) & SPI_STAT_BUSY);
}

// Waits until no chain is active, looking twice 1 us apart: a request taken just before a mask shows within a few
// cycles.
static bool WaitChainIdle() {
    const uint32_t start = CycleCounter::Now();
    const uint32_t settle = CycleCounter::kCpuHz / 1000000;
    const uint32_t limit = kWaitMaxUs * (CycleCounter::kCpuHz / 1000000);
    while (true) {
        const uint32_t elapsed = CycleCounter::Since(start);
        if (!ChainActive() && elapsed >= settle) {
            return true;
        }
        if (elapsed > limit) {
            counters_.wait_timeouts++;
            return false;
        }
    }
}

void Arm() {
    if (!running || armed || !SpiIdle()) {  // A chain pushes bytes into the TX FIFO.
        return;
    }
    uintptr_t key = HwiP_disable();
    // Latched high: no edge can come until a clear, so the software request is the only start.
    const bool latched = mlat_capture::PinHigh();
    HWREG(UDMA0_BASE + UDMA_O_CLEARREQMASK) = kClearBit;
    if (latched) {
        HWREG(UDMA0_BASE + UDMA_O_SOFTREQ) = kClearBit;
        counters_.kicks++;
    }
    armed = true;
    HwiP_restore(key);
}

bool ClearPending() {
    if (!running || armed || !mlat_capture::PinHigh() || chain_busy != 0 || !SpiIdle()) {
        return false;
    }
    uintptr_t key = HwiP_disable();
    HWREG(UDMA0_BASE + UDMA_O_SOFTREQ) = kClearBit;  // Software requests are not masked.
    WaitChainIdle();
    FlushRx();
    counters_.pending_clears++;
    HwiP_restore(key);
    return true;
}

bool Disarm() {
    if (!running) {
        return true;
    }
    uintptr_t key = HwiP_disable();
    if (!armed) {
        HwiP_restore(key);
        return true;
    }
    HWREG(UDMA0_BASE + UDMA_O_SETREQMASK) = kClearBit;
    armed = false;
    const bool ok = WaitChainIdle();
    FlushRx();
    HwiP_restore(key);
    return ok;
}

const Counters& counters() { return counters_; }
void ResetCounters() { counters_ = Counters(); }

}  // namespace mlat_clear_dma
