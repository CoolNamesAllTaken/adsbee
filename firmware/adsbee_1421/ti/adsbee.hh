#pragma once

#include "aircraft_dictionary.hh"
#include "bsp.hh"
#include "lr2021.hh"
#include "settings.hh"

class ADSBee {
   public:
    static constexpr uint32_t kDefaultWatchdogTimeoutSec = 10;

    struct ADSBeeConfig {
        LR2021::LR2021Config lr2021_config = {
            .spi_index = bsp.kCoProSPIIndex,
            .gpio_nss = bsp.kLR2021CSPin,
            .gpio_busy = bsp.kLR2021BusyPin,
            .gpio_enable = bsp.kLR2021ResetPin,
            .gpio_sclk = bsp.kCoProSPICLKPin,
            .gpio_pico = bsp.kCoProSPIMOSIPin,
        };
        uint32_t aircraft_dictionary_update_interval_ms = 1000;
        uint32_t rx_position_update_interval_ms = 1000;
    };

    ADSBee(ADSBeeConfig config);

    bool Init();
    bool Update();

    void SetRx1090Enabled(bool enabled) { rx_1090_enabled_ = enabled; }
    bool Rx1090IsEnabled() const { return rx_1090_enabled_; }
    // Sub-GHz receiver enable is owned by SubGHzRadio (it must open/close the RF core); these forward to it.
    // SetRxSubGHzEnabled() returns false if the RF client failed to open/close.
    bool SetRxSubGHzEnabled(bool enabled);
    bool RxSubGHzIsEnabled() const;

    bool SetWatchdogTimeoutSec(uint32_t timeout_sec);
    inline uint32_t GetWatchdogTimeoutSec() const { return watchdog_timeout_sec_; }
    // Pets the watchdog if it is running. Lets long-running blocking operations (e.g. the CW test) avoid a reset.
    void FeedWatchdog();

    // Mode S receiver sync mode (how the LR2021 triggers reception). Re-applies the receiver config.
    void SetR1090PreambleMode(SettingsManager::R1090PreambleMode mode);
    SettingsManager::R1090PreambleMode GetR1090PreambleMode() const { return r1090_preamble_mode_; }
    // LF-frontend AGC gain (0 = auto, 1..15 manual; 13 = max). Re-applies the receiver config.
    void SetR1090Gain(uint8_t gain_step);
    uint8_t GetR1090Gain() const { return r1090_gain_; }
    // LF RX path boost (0 = off .. 7 = max). Re-applies the receiver config.
    void SetR1090RxBoost(uint8_t rx_boost);
    uint8_t GetR1090RxBoost() const { return r1090_rx_boost_; }

    void Reboot();
    void EnterUARTBootloader();

    // True when an external host has asserted SYNC to request the LR2021 bus + MCU sleep. Latched by the
    // SYNC rising-edge ISR (which also hands the bus off immediately: tri-state + command abort) with a
    // live pin-level fallback for the no-edge cases (SYNC already high at boot, interrupt disarmed).
    // The main loop polls this and calls EnterSyncSleep() for the graceful half.
    bool SyncSleepRequested();

    // Enters MCU STANDBY (deep sleep, SRAM retained) while an external host holds the SYNC line HIGH,
    // and blocks until the host drives SYNC LOW. The SYNC ISR has usually already tri-stated the shared
    // LR2021 bus within microseconds of the edge; this finishes the job (SPI teardown, wake-interrupt
    // swap, STANDBY loop) and re-runs the full receiver re-init on wake. The caller must quiesce the
    // SubGHz RF core (SubGHzRadio::Suspend()) before calling this, otherwise its power constraint
    // prevents the MCU from reaching STANDBY.
    void EnterSyncSleep();

    LR2021 lr2021;
    AircraftDictionary aircraft_dictionary;

    // Health / diagnostics counter, reported and reset via AT+RX_STATS. Incremented when the LR2021
    // RX FIFO reads back completely full (the poll loop fell behind; frames were likely dropped).
    uint32_t lr2021_fifo_full_count = 0;

    // Longest single super-loop iteration observed, in microseconds. Reported and reset via AT+RX_STATS. Every
    // millisecond spent in one iteration is a millisecond the LR2021 FIFO isn't drained and AT commands aren't
    // serviced, so this is the primary "is the receiver bogging down" gauge. Updated by main().
    uint32_t max_loop_us = 0;

    SettingsManager::RxPosition rx_position;
    bool rx_position_available = false;

   private:
    void IngestAndForwardPackets();
    void PruneAircraftDictionary();
    // Periodically refreshes rx_position / rx_position_available from the configured source (e.g. the
    // lowest airborne aircraft) and pushes the result into the aircraft dictionary's reference position,
    // which gates Mode S surface position decoding. Ported from the ADSBee 1090.
    void UpdateRxPosition();
    bool UpdateLR2021();
    // (Re)applies the current receiver configuration (sync mode, gain, CRC filter) to the LR2021.
    bool ApplyReceiverConfig();

    ADSBeeConfig config_;

    bool rx_1090_enabled_ = false;

    SettingsManager::R1090PreambleMode r1090_preamble_mode_ = SettingsManager::kR1090PreambleModeModeS;
    uint8_t r1090_gain_ = 10;      // 0 = auto, 1..15 manual (13 = max). Default: manual step 10.
    uint8_t r1090_rx_boost_ = 0;  // LF RX path boost, 0 (off) .. 7 (max).

    uint32_t last_aircraft_dictionary_update_timestamp_ms_ = 0;
    uint32_t last_rx_position_update_timestamp_ms_ = 0;

    uint32_t watchdog_timeout_sec_ = kDefaultWatchdogTimeoutSec;

    uint8_t lr2021_rx_buf_[LR2021::kRxFifoMaxDepthBytes];
};

extern ADSBee adsbee;