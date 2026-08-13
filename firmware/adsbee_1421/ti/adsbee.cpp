#include "adsbee.hh"

#include <ti/devices/cc13x4_cc26x4/driverlib/ccfgread.h>
#include <ti/devices/cc13x4_cc26x4/driverlib/osc.h>
#include <ti/devices/cc13x4_cc26x4/driverlib/sys_ctrl.h>
#include <ti/devices/cc13x4_cc26x4/driverlib/watchdog.h>
#include <ti/drivers/GPIO.h>
#include <ti/drivers/Power.h>
#include <ti/drivers/power/PowerCC26XX.h>

#include "buffer_utils.hh"
#include "comms.hh"
#include "flash_utils.hh"
#include "led.hh"
#include "packet_decoder.hh"
#include "uat_packet_decoder.hh"

ADSBee::ADSBee(ADSBeeConfig config) : lr2021(config.lr2021_config), config_(config) {}

// Set from the SYNC rising-edge ISR; cleared in EnterSyncSleep() once SYNC has dropped. The level
// fallback in SyncSleepRequested() covers the cases where no edge ever fires (SYNC already high at
// boot) or the interrupt is momentarily disarmed.
static volatile bool sync_sleep_requested_ = false;

// SYNC line ISR, armed for a RISING edge while awake and a FALLING edge while asleep (CC26XX/CC13x4
// GPIO interrupts are edge-only). Reads the live pin level rather than trusting the armed edge, so
// stale latched EVFLAGS events and bounces are benign, and re-running the handoff is idempotent.
//
// SYNC high: performs the time-critical half of sync sleep -- the electrical handoff of the shared
// LR2021 bus to the external host -- within microseconds of the edge, even if an SPI transfer is in
// flight (the DMA completes internally against the un-muxed pins). Everything here is GPIO register
// work and volatile stores, all HWI-safe. The graceful half (draining output, suspending peripherals,
// STANDBY) runs from the main loop via SyncSleepRequested().
//
// SYNC low: nothing to do -- its only job is waking the MCU from STANDBY; execution resumes right
// after the PowerCC26XX_standbyPolicy() call in EnterSyncSleep().
static void SyncLineCallback(uint_least8_t /*index*/) {
    if (GPIO_read(bsp.kSyncPin) == 1) {
        sync_sleep_requested_ = true;
        adsbee.lr2021.RequestAbort();       // Unwind any in-progress command sequence at the next boundary.
        adsbee.lr2021.TristateInterface();  // Release NSS/ENABLE/SCLK/PICO to the host immediately.
    }
}

bool ADSBee::Init() {
    // Arm the SYNC rising-edge interrupt (the SysConfig default pin config) before touching the LR2021,
    // so a host asserting SYNC mid-init still gets the bus handed off promptly. Clear any stale latched
    // edge first: neither GPIO_setConfig nor GPIO_enableInt clears EVFLAGS.
    GPIO_setCallback(bsp.kSyncPin, SyncLineCallback);
    GPIO_clearInt(bsp.kSyncPin);
    GPIO_enableInt(bsp.kSyncPin);
    return ApplyReceiverConfig();
}

bool ADSBee::SyncSleepRequested() { return sync_sleep_requested_ || GPIO_read(bsp.kSyncPin) == 1; }

bool ADSBee::ApplyReceiverConfig() {
    // Reconfigure from a clean hardware reset every time. The LR2021's RF/AGC/detector calibration
    // must be set up from standby (kStdbyRC); reconfiguring while the radio is in continuous RX
    // leaves it demodulating but never validating. DeInit()+Init() reproduces the exact known-good
    // boot sequence (reset -> kStdbyRC) before configuring, for both boot and live AT changes.
    lr2021.DeInit();  // Safe even if never inited (SPI_close is guarded).
    if (!lr2021.Init()) {
        return false;
    }
    return lr2021.SetOokADSB(r1090_preamble_mode_, r1090_gain_, r1090_rx_boost_);
}

void ADSBee::SetR1090PreambleMode(SettingsManager::R1090PreambleMode mode) {
    if (mode >= SettingsManager::kNumR1090PreambleModes) {
        // Guard against stale persisted settings holding a removed enum value.
        mode = SettingsManager::kR1090PreambleModeModeS;
    }
    r1090_preamble_mode_ = mode;
    ApplyReceiverConfig();
}

void ADSBee::SetR1090Gain(uint8_t gain_step) {
    r1090_gain_ = gain_step;
    ApplyReceiverConfig();
}

void ADSBee::SetR1090RxBoost(uint8_t rx_boost) {
    r1090_rx_boost_ = rx_boost;
    ApplyReceiverConfig();
}

void ADSBee::EnterSyncSleep() {
    // Disarm the rising-edge interrupt while we reconfigure the pin for wake. The time-critical bus
    // handoff has already run in SyncLineCallback (or is redone idempotently below, for the level-poll
    // entry path where no edge ever fired, e.g. SYNC already high at boot).
    GPIO_disableInt(bsp.kSyncPin);

    CONSOLE_INFO("ADSBee::EnterSyncSleep", "SYNC asserted; powering down LR2021 and entering STANDBY.");

    // Finish powering the external radio down. The ISR already tri-stated the bus; DeInit()'s enable-low
    // write is then a harmless DOUT update on an input pin, and SPI_close leaves SCLK/PICO hi-Z (their
    // SysConfig not-in-use configs are inputs). ApplyReceiverConfig() below re-runs the exact boot
    // sequence on wake.
    lr2021.DeInit();

    // Re-assert the tri-state (idempotent): covers the poll-path entry where SyncLineCallback never ran.
    // RestoreInterface() below re-drives NSS/ENABLE on wake.
    lr2021.TristateInterface();

    // Re-arm SYNC (DIO_5) as the STANDBY wake source on a FALLING edge (SYNC going low). CC26XX/CC13x4
    // hardware does not support level-triggered GPIO interrupts, so an edge is the only option. The
    // lost-edge race (host drops SYNC between the GPIO_read below and entering STANDBY) is closed by the
    // re-check loop: with the interrupt enabled, the edge latches as a pending NVIC interrupt, the
    // policy's WFI returns immediately, and the loop re-reads LOW and exits. Keep the fail-safe pull-down,
    // and clear any stale latched edge before enabling (EVFLAGS is not cleared by setConfig/enableInt).
    GPIO_setConfig(bsp.kSyncPin, GPIO_CFG_INPUT_INTERNAL | GPIO_CFG_IN_INT_FALLING | GPIO_CFG_PULL_DOWN_INTERNAL);
    GPIO_setCallback(bsp.kSyncPin, SyncLineCallback);
    GPIO_clearInt(bsp.kSyncPin);
    GPIO_enableInt(bsp.kSyncPin);

    // Let the console line go fully idle before sampling constraints below. UART2 holds
    // PowerCC26XX_DISALLOW_STANDBY from the start of a TX until its EOT interrupt, which lands after the
    // last stop bit -- well after the write callback that iface_write()'s blocking wait keys off. Without
    // this the CONSOLE_INFO above guarantees a spurious "STANDBY blocked" report on every sleep cycle.
    comms_manager.DrainConsoleTx();

    // On CC13x4 an enabled DIO interrupt is automatically a STANDBY wake source (the GPIO driver routes
    // PAD events to MCU WU1 at init), so no explicit AON/IOC wakeup config is needed.
    //
    // PowerCC26XX_standbyPolicy() is what performs the constraint-checked WFI/IDLE/STANDBY transition,
    // but it short-circuits and returns immediately unless the GLOBAL power policy is enabled
    // (PowerCC26X2_nortos.c: `if (!PowerCC26X2_module.enablePolicy) return;` is its first statement),
    // and main.cpp deliberately disables the policy at boot for debugger stability. Without the enable
    // below the loop is a pure busy-spin that never sleeps at all. Scope the enable to the sleep loop
    // and restore the caller's setting on wake, so the rest of the firmware keeps running with the
    // policy off. Power_disablePolicy() returns the previous state, so it doubles as the read.
    bool policy_was_enabled = Power_disablePolicy();
    Power_enablePolicy();

    // Re-check SYNC in a loop because the policy can return from a plain WFI/IDLE (e.g. a pending ClockP
    // tick) without having reached STANDBY, or while a power constraint is still momentarily held (e.g. a
    // UART/SPI transfer draining). The caller must have quiesced the persistent constraint holders (the
    // SubGHz RF core and the console UART RX) first, or the policy will never descend to STANDBY.
    //
    // Constraint diagnostics: a briefly-held constraint (the CONSOLE_INFO above draining, an SPI transfer
    // finishing) clears on its own and is not worth reporting, so only start complaining once STANDBY has
    // been blocked continuously for kConstraintGraceMs, then repeat at kConstraintRepeatMs so a genuinely
    // stuck holder keeps reporting without flooding the console.
    static constexpr uint32_t kConstraintGraceMs = 250;
    static constexpr uint32_t kConstraintRepeatMs = 1000;
    uint32_t unblocked_timestamp_ms = get_time_since_boot_ms();
    uint32_t next_warning_timestamp_ms = unblocked_timestamp_ms + kConstraintGraceMs;
    while (GPIO_read(bsp.kSyncPin) == 1) {
        uint32_t constraint_mask = Power_getConstraintMask();
        uint32_t timestamp_ms = get_time_since_boot_ms();
        if (!(constraint_mask & (1u << PowerCC26XX_DISALLOW_STANDBY))) {
            unblocked_timestamp_ms = timestamp_ms;
            next_warning_timestamp_ms = timestamp_ms + kConstraintGraceMs;
        } else if (static_cast<int32_t>(timestamp_ms - next_warning_timestamp_ms) >= 0) {
            // Report the LF clock state alongside the mask. Power_init() takes DISALLOW_STANDBY pending
            // the SCLK_LF switch and only releases it once the LF clock actually reaches RCOSC_LF or
            // XOSC_LF, so a CCFG that asks for LF XOSC (option 2) on a board whose 32.768 kHz crystal
            // is absent or not oscillating pins this constraint from boot forever. lf_src is the live
            // OSC_{RCOSC,XOSC}_{HF,LF} value; ccfg_lf is the configured CCFG SCLK_LF_OPTION.
            CONSOLE_WARNING("ADSBee::EnterSyncSleep",
                            "STANDBY blocked for %lums; constraint mask = 0x%lx, lf_src = %lu, ccfg_lf = %lu.",
                            (unsigned long)(timestamp_ms - unblocked_timestamp_ms), (unsigned long)constraint_mask,
                            (unsigned long)OSCClockSourceGet(OSC_SRC_CLK_LF),
                            (unsigned long)CCFGRead_SCLK_LF_OPTION());
            next_warning_timestamp_ms = timestamp_ms + kConstraintRepeatMs;
            // The warning itself is a TX, which re-takes the very constraint we are reporting on. Drain
            // it so the next pass measures the real holder instead of confirming its own echo.
            comms_manager.DrainConsoleTx();
        }
        PowerCC26XX_standbyPolicy();
        // The CC13x4 watchdog keeps counting (on SCLK_LF) through STANDBY, so feed it on every policy
        // return or a long enough sleep watchdog-resets the MCU mid-sleep.
        FeedWatchdog();
    }

    if (!policy_was_enabled) {
        Power_disablePolicy();
    }

    // SYNC is now low: swap the wake interrupt back to the rising-edge sleep-request config (keeping the
    // fail-safe pull-down), clear the request flag, then re-initialize the receiver to resume where we
    // left off. If SYNC bounces high during the re-init, the re-armed ISR re-tristates and sets the flag
    // again, the config aborts, and the main loop re-enters sync sleep.
    GPIO_disableInt(bsp.kSyncPin);
    sync_sleep_requested_ = false;
    GPIO_setConfig(bsp.kSyncPin, GPIO_CFG_INPUT_INTERNAL | GPIO_CFG_IN_INT_RISING | GPIO_CFG_PULL_DOWN_INTERNAL);
    GPIO_clearInt(bsp.kSyncPin);
    GPIO_enableInt(bsp.kSyncPin);
    FeedWatchdog();

    CONSOLE_INFO("ADSBee::EnterSyncSleep", "SYNC released; re-initializing LR2021.");
    // Re-drive NSS/ENABLE (tri-stated above) before ApplyReceiverConfig()'s Init() drives them via
    // GPIO_write; the SPI pins are re-muxed by SPI_open() inside Init().
    lr2021.RestoreInterface();
    ApplyReceiverConfig();
}

void ADSBee::FeedWatchdog() {
    if (WatchdogRunning()) {
        WatchdogIntClear();
    }
}

bool ADSBee::Update() {
    FeedWatchdog();
    UpdateLR2021();
    PruneAircraftDictionary();
    UpdateRxPosition();
    IngestAndForwardPackets();
    return true;
}

void ADSBee::UpdateRxPosition() {
    // Rate limiting.
    uint32_t timestamp_ms = get_time_since_boot_ms();
    if (timestamp_ms - last_rx_position_update_timestamp_ms_ < config_.rx_position_update_interval_ms) {
        return;
    }
    last_rx_position_update_timestamp_ms_ = timestamp_ms;

    // Update rx position based on selected position source. Note this only handles periodic automatic updates.
    // One-time changes are handled in AT comms.
    switch (rx_position.source) {
        case SettingsManager::RxPosition::PositionSource::kPositionSourceNone:
            // No position available.
            rx_position_available = false;
            break;
        case SettingsManager::RxPosition::PositionSource::kPositionSourceLowestAircraft: {
            // Use position of lowest aircraft in dictionary.
            // Make variables to write into since we can't bind directly to the packed struct members.
            float latitude_deg, longitude_deg, heading_deg;
            int32_t gnss_altitude_ft, baro_altitude_ft, speed_kts;
            if (aircraft_dictionary.GetLowestAircraftPosition(latitude_deg, longitude_deg, gnss_altitude_ft,
                                                              baro_altitude_ft, heading_deg, speed_kts)) {
                rx_position.latitude_deg = latitude_deg;
                rx_position.longitude_deg = longitude_deg;
                rx_position.gnss_altitude_ft = gnss_altitude_ft;
                rx_position.baro_altitude_ft = baro_altitude_ft;
                rx_position.heading_deg = heading_deg;
                rx_position.speed_kts = speed_kts;
                rx_position_available = true;
            } else {
                // No valid aircraft position available. Don't update receiver position.
                rx_position_available = false;
            }
            break;
        }
        case SettingsManager::RxPosition::PositionSource::kPositionSourceGNSS:
            // No GNSS receiver on this board; position must come from another source.
            rx_position_available = false;
            break;
        case SettingsManager::RxPosition::PositionSource::kPositionSourceFixed:
            // Fixed position is always available.
            rx_position_available = true;
            break;
        case SettingsManager::RxPosition::PositionSource::kPositionSourceAircraftMatchingICAO: {
            // Try to find the aircraft with the matching ICAO address in the dictionary.
            // Check both Mode S and UAT, and use the most recently seen aircraft if both exist.
            uint32_t mode_s_uid = Aircraft::ICAOToUID(rx_position.icao_address, Aircraft::kAircraftTypeModeS);
            ModeSAircraft* mode_s_aircraft = aircraft_dictionary.GetAircraftPtr<ModeSAircraft>(mode_s_uid, false);
            bool mode_s_valid = mode_s_aircraft && mode_s_aircraft->HasBitFlag(ModeSAircraft::kBitFlagPositionValid);

            uint32_t uat_uid = Aircraft::ICAOToUID(rx_position.icao_address, Aircraft::kAircraftTypeUAT);
            UATAircraft* uat_aircraft = aircraft_dictionary.GetAircraftPtr<UATAircraft>(uat_uid, false);
            bool uat_valid = uat_aircraft && uat_aircraft->HasBitFlag(UATAircraft::kBitFlagPositionValid);

            // Determine which aircraft to use based on validity and recency.
            Aircraft* selected_aircraft = nullptr;
            if (mode_s_valid && uat_valid) {
                // Both exist and have valid positions; use the most recently seen.
                if (mode_s_aircraft->last_message_timestamp_ms >= uat_aircraft->last_message_timestamp_ms) {
                    selected_aircraft = mode_s_aircraft;
                } else {
                    selected_aircraft = uat_aircraft;
                }
            } else if (mode_s_valid) {
                selected_aircraft = mode_s_aircraft;
            } else if (uat_valid) {
                selected_aircraft = uat_aircraft;
            }

            if (selected_aircraft) {
                rx_position.latitude_deg = selected_aircraft->latitude_deg;
                rx_position.longitude_deg = selected_aircraft->longitude_deg;
                rx_position.gnss_altitude_ft = selected_aircraft->gnss_altitude_ft;
                rx_position.baro_altitude_ft = selected_aircraft->baro_altitude_ft;
                rx_position.heading_deg = selected_aircraft->direction_deg;
                rx_position.speed_kts = selected_aircraft->speed_kts;
                rx_position_available = true;
            } else {
                // No aircraft found with the matching ICAO address or no valid position.
                rx_position_available = false;
            }
            break;
        }
        default:
            CONSOLE_ERROR("ADSBee::UpdateRxPosition", "Unknown Rx position source %d.",
                          static_cast<int>(rx_position.source));
    }

    // Update the aircraft dictionary's reference location. Clearing it when unavailable pauses Mode S
    // surface position decoding, which would otherwise resolve CPR against a stale or bogus reference.
    if (rx_position_available) {
        aircraft_dictionary.SetReferencePosition(rx_position.latitude_deg, rx_position.longitude_deg);
    } else {
        aircraft_dictionary.ClearReferencePosition();
    }
}

bool ADSBee::SetWatchdogTimeoutSec(uint32_t timeout_sec) {
    // timeout_sec == 0 means disabled; don't start the watchdog. Note: if the watchdog is already
    // running it cannot be stopped in hardware, so Update() will continue feeding it via WatchdogRunning().
    if (timeout_sec == 0) {
        watchdog_timeout_sec_ = 0;
        return true;
    }

    // Guard against overflow: max load value is UINT32_MAX ticks at GET_MCU_CLOCK Hz.
    if (timeout_sec > UINT32_MAX / GET_MCU_CLOCK) {
        return false;
    }

    watchdog_timeout_sec_ = timeout_sec;

    WatchdogUnlock();
    WatchdogReloadSet(timeout_sec * GET_MCU_CLOCK);
    if (!WatchdogRunning()) {
        WatchdogResetEnable();
        WatchdogEnable();
    }
    WatchdogLock();

    return true;
}

void ADSBee::Reboot() {
    CONSOLE_INFO("ADSBee::Reboot", "Rebooting.");
    lr2021.DeInit();
    SysCtrlSystemReset();
}

void ADSBee::EnterUARTBootloader() {
    CONSOLE_INFO("ADSBee::EnterUARTBootloader", "Invalidating image and entering ROM UART bootloader.");
    lr2021.DeInit();
    // Mask interrupts and keep them masked through the reset: we are about to erase the vector
    // table sector, so no interrupt may fire afterwards. FlashSectorErase() and
    // SysCtrlSystemReset() both execute from ROM, so erasing flash sector 0 from here is safe.
    // Do not add any work between the erase and the reset.
    FlashUtils::FlashSafe();
    FlashUtils::EraseSector(0x0);  // erase the vector-table sector -> invalid reset vector
    // With CCFG IMAGE_VALID_CONF == 0, the ROM validates the reset vector at flash address 0x0
    // on boot. With it erased (0xFFFFFFFF) the ROM treats the image as invalid and enters the
    // serial bootloader on DIO2 (RX) / DIO3 (TX) -- the same pins as SUBG_UART.
    SysCtrlSystemReset();
    // Does not return.
}

/**
 * Private Functions
 */

void ADSBee::IngestAndForwardPackets() {
    // Ingest new Mode S packets into dictionary and report them.
    DecodedModeSPacket decoded_packet;
    // Explicitly count the number of packets to process so that we don't get stuck in this loop if the decoder
    // keeps outputting packets.
    uint16_t num_decoded_mode_s_packets = packet_decoder.decoded_mode_s_packet_out_queue.Length();
    for (uint16_t i = 0;
         i < num_decoded_mode_s_packets && packet_decoder.decoded_mode_s_packet_out_queue.Dequeue(decoded_packet);
         i++) {
        // CONSOLE_INFO("ADSBee::IngestAndForwardPackets", "\tdf=%d icao_address=0x%06x",
        // decoded_packet.downlink_format,
        //              decoded_packet.icao_address);

        if (aircraft_dictionary.IngestDecodedModeSPacket(decoded_packet)) {
            // Packet was used to update the dictionary or was silently ignored (but presumed to be valid).
            leds.FlashLED(bsp.k1090LEDPin, 10);
            // CONSOLE_INFO("ADSBee::IngestAndForwardPackets", "\taircraft_dictionary: %d aircraft",
            //              aircraft_dictionary.GetNumAircraft());
        }
        // Check for any new valid packets and push all decoded packets to the reporting queue, even if the aircraft
        // dictionary didn't know what to do with them.
        if (decoded_packet.is_valid) {
            if (!comms_manager.mode_s_packet_reporting_queue.Enqueue(decoded_packet.raw)) {
                CONSOLE_ERROR("ADSBee::IngestAndForwardPackets", "Mode S packet reporting queue overflowed.");
            }
        }
    }

    // Ingest decoded UAT ADS-B packets.
    DecodedUATADSBPacket decoded_uat_adsb_packet;
    uint16_t num_decoded_uat_adsb = uat_packet_decoder.decoded_uat_adsb_packet_out_queue.Length();
    for (uint16_t i = 0; i < num_decoded_uat_adsb &&
                         uat_packet_decoder.decoded_uat_adsb_packet_out_queue.Dequeue(decoded_uat_adsb_packet);
         i++) {
        aircraft_dictionary.IngestDecodedUATADSBPacket(decoded_uat_adsb_packet);
        aircraft_dictionary.RecordSubGHzMetrics(0, 1, 0, 0);
        if (!comms_manager.uat_adsb_packet_reporting_queue.Enqueue(decoded_uat_adsb_packet.raw)) {
            CONSOLE_ERROR("ADSBee::IngestAndForwardPackets", "UAT ADS-B packet reporting queue overflowed.");
        }
    }

    // Ingest decoded UAT uplink packets. The raw packet has already been FEC-corrected in place by the
    // decoder, so downstream reporters (e.g. GDL90) can re-decode it without another correction pass.
    DecodedUATUplinkPacket decoded_uat_uplink_packet;
    uint16_t num_decoded_uat_uplink = uat_packet_decoder.decoded_uat_uplink_packet_out_queue.Length();
    for (uint16_t i = 0; i < num_decoded_uat_uplink &&
                         uat_packet_decoder.decoded_uat_uplink_packet_out_queue.Dequeue(decoded_uat_uplink_packet);
         i++) {
        aircraft_dictionary.RecordSubGHzMetrics(0, 0, 0, 1);
        if (!comms_manager.uat_uplink_packet_reporting_queue.Enqueue(decoded_uat_uplink_packet.raw)) {
            CONSOLE_ERROR("ADSBee::IngestAndForwardPackets", "UAT uplink packet reporting queue overflowed.");
        }
    }
}

void ADSBee::PruneAircraftDictionary() {
    // Prune aircraft dictionary. Need to do this up front so that we don't end up with a negative timestamp delta
    // caused by packets being ingested more recently than the timestamp we take at the beginning of this function.
    uint32_t timestamp_ms = get_time_since_boot_ms();
    if (timestamp_ms - last_aircraft_dictionary_update_timestamp_ms_ > config_.aircraft_dictionary_update_interval_ms) {
        aircraft_dictionary.Update(timestamp_ms);

        last_aircraft_dictionary_update_timestamp_ms_ = timestamp_ms;
    }
}

bool ADSBee::UpdateLR2021() {
    // Once the SYNC ISR has handed the bus to the host, issue no further transactions and stay quiet:
    // any in-progress calls below fail via the abort flag, which is expected, not an error. The main
    // loop enters sync sleep at the top of its next iteration.
    if (SyncSleepRequested()) {
        return true;
    }
    LR2021::GetAndClearIrqRsp rsp{};
    if (!lr2021.GetAndClearIrq(&rsp)) {
        if (!SyncSleepRequested()) {
            CONSOLE_ERROR("ADSBee::Update", "Failed to get LR2021 IRQs.");
        }
        return false;
    }

    // if (rsp.irq_flags & LR2021::HostIrqs::kIrqPreambleDetected) {
    //     leds.FlashLED(bsp.k1090LEDPin, 50);  // Flash the LED for 50ms.
    //     CONSOLE_INFO("ADSBee::Update", "LR2021 detected a preamble.");
    // }
    if (rsp.irq_flags & LR2021::HostIrqs::kIrqRxFifo) {
        // leds.FlashLED(bsp.k1090LEDPin, 20);  // Flash the LED for 100ms.
        LR2021::FifoLevelRsp rx_fifo_level_rsp;
        if (!lr2021.GetRxFifoLevel(&rx_fifo_level_rsp)) {
            if (!SyncSleepRequested()) {
                CONSOLE_ERROR("ADSBee::Update", "Failed to get LR2021 Rx FIFO level.");
            }
            return false;
        }
        if (rx_fifo_level_rsp.level == 0) {
            return true;  // IRQ fired but FIFO is empty (threshold crossed in both directions).
        }
        if (rx_fifo_level_rsp.level >= LR2021::kRxFifoMaxDepthBytes) {
            // FIFO read back completely full: the poll loop fell behind and the radio almost certainly
            // dropped frames on top of this. Counted (not just logged) so benches can see it via
            // AT+RX_STATS even with logging off.
            lr2021_fifo_full_count++;
        }
        if (rx_fifo_level_rsp.level > sizeof(lr2021_rx_buf_)) {
            CONSOLE_ERROR("ADSBee::Update", "LR2021 Rx FIFO level %u exceeds buffer size %zu.", rx_fifo_level_rsp.level,
                          sizeof(lr2021_rx_buf_));
            return false;
        }
        if (!lr2021.ReadRxFifo(lr2021_rx_buf_, rx_fifo_level_rsp.level)) {
            if (!SyncSleepRequested()) {
                CONSOLE_ERROR("ADSBee::Update", "Failed to read LR2021 Rx FIFO.");
            }
            return false;
        }

        // The FIFO packet length depends on the preamble mode: DF17 mode captures a shorter
        // remainder because the detector consumed the preamble + DF17 header bits.
        const bool df17_mode = LR2021::IsOokDF17PreambleMode(r1090_preamble_mode_);
        const uint16_t packet_len_bytes = LR2021::GetOokRxPacketLenBytes(r1090_preamble_mode_);
        uint16_t num_packets = packet_len_bytes ? (rx_fifo_level_rsp.level / packet_len_bytes) : 0;
        for (uint16_t i = 0; i < num_packets; i++) {
            uint8_t* packet_start = lr2021_rx_buf_ + i * packet_len_bytes;

            uint32_t rx_word_buf[RawModeSPacket::kMaxPacketLenWords32] = {0};
            if (df17_mode) {
                // Reconstruct the full 112-bit frame by prepending the known DF=17 header bits
                // (which the detector consumed) in front of the captured remainder, so the decoder +
                // software CRC validate the whole frame.
                const LR2021::OokDetectorConfig& detector = LR2021::kOokDF17Detector;
                SetNBitsInWordBuffer(detector.header_len_bits, detector.header_bits, 0, rx_word_buf);
                uint32_t remainder_words[RawModeSPacket::kMaxPacketLenWords32] = {0};
                ByteBufferToWordBuffer(packet_start, remainder_words, packet_len_bytes);
                const uint16_t remainder_bits = packet_len_bytes * 8;
                for (uint16_t b = 0; b < remainder_bits; b += 8) {
                    uint16_t chunk = (remainder_bits - b) < 8 ? (remainder_bits - b) : 8;
                    uint32_t val = GetNBitsFromWordBuffer(chunk, b, remainder_words);
                    SetNBitsInWordBuffer(chunk, val, detector.header_len_bits + b, rx_word_buf);
                }
            } else {
                ByteBufferToWordBuffer(packet_start, rx_word_buf, packet_len_bytes);
            }
            RawModeSPacket raw_packet(rx_word_buf, RawModeSPacket::kExtendedSquitterPacketNumWords32);
            raw_packet.mlat_48mhz_64bit_counts = get_time_since_boot_us() * 48;
            // Record demod + raw frame metrics (valid frames are recorded during dictionary
            // ingestion). All LR2021 captures are 112-bit extended-squitter-length frames.
            aircraft_dictionary.Record1090Demod();
            aircraft_dictionary.Record1090RawExtendedSquitterFrame();
            if (packet_decoder.raw_mode_s_packet_queue.IsFull()) {
                packet_decoder.raw_queue_overflow_count++;
            }
            packet_decoder.raw_mode_s_packet_queue.Enqueue(raw_packet);
        }
    }
    return true;
}