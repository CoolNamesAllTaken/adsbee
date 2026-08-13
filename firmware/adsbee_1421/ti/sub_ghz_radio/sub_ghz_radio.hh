#pragma once

extern "C" {
#include <ti/drivers/GPIO.h>
#include <ti/drivers/rf/RF.h>
#include <ti_radio_config.h>

#include "smartrf/smartrf_settings.h"

/* clang-format off */
#include <ti/devices/DeviceFamily.h>
#include DeviceFamily_constructPath(driverlib/rf_data_entry.h)
/** clang-format on */
}

#include "bsp.hh"
// #include "buffer_utils.hh"
#include "comms.hh"
#include "unit_conversions.hh"
#include "uat_packet.hh"

class SubGHzRadio
{
public:
    // Partial data entries in the RF core's circular RX queue. Sized so back-to-back receptions don't
    // exhaust entries (PROP_ERROR_RXBUF) while the main loop is busy elsewhere; each entry is
    // ~(kRxPacketMaxLenBytes + overhead) bytes of static RAM.
    static const uint16_t kRxPacketQueueLen = 4;
    static const uint16_t kRxPacketMaxLenBytes = RawUATUplinkPacket::kUplinkMessageNumBytes;

    struct SubGHzRadioConfig
    {
        // Add any configuration parameters needed for the SubGHzRadio.
    };

    SubGHzRadio(SubGHzRadioConfig config_in): config_(config_in) {};
    ~SubGHzRadio() {};

    /**
     * Initializes the radio and begins packet reception.
     */
    bool Init();

    /**
     * De-initializes the radio.
     */
    bool DeInit();

    /**
     * Enables or disables the bias tee.
     * @param enabled True to enable the bias tee, false to disable it.
     */
    inline void SetBiasTeeEnable(bool enabled) {
        // No bias tee pin on CC1314 hardware.
        CONSOLE_INFO("SubGHzRadio::SetBiasTeeEnable", "Bias tee %s (no-op on CC1314)", enabled ? "ENABLED" : "DISABLED");
    }
    /**
     * Begin the proprietary RF receive command.
     * @retval True if command was posted successfully, false otherwise.
     */
    bool StartPacketRx();

    /**
     * Starts a packet Rx if it hasn't been started and we are currently supposed to be receiving, plus some other housekeeping.
     * @retval True if update succeeded, false otherwise.
     */
    bool Update();

    /**
     * Quiesces the internal RF core so the MCU can enter STANDBY. Cancels the in-progress RX command
     * and closes the RF client, which releases the PowerCC26XX_DISALLOW_STANDBY constraint the RF core
     * holds while powered. Reuses the known-good DeInit() (RF_close) path. Pair with Resume() on wake.
     * @retval True if the radio was suspended successfully, false otherwise.
     */
    bool Suspend();

    /**
     * Re-establishes UAT reception after a Suspend()/STANDBY cycle by re-running the full Init()
     * (RF_open + CMD_FS + StartPacketRx) restore path.
     * @retval True if the radio resumed successfully, false otherwise.
     */
    bool Resume();

    /**
     * Handles a received packet from the RF core.
     * @param filled_entry Pointer to the filled data entry from the RF core.
     * @retval True if packet was handled successfully, false otherwise.
     */
    bool HandlePacketRx(rfc_dataEntryPartial_t *filled_entry);

#ifdef HARDWARE_UNIT_TESTS
    /**
     * Starts an unmodulated continuous-wave (CW) carrier for testing. Cancels any in-progress packet
     * reception and keeps the carrier on until StopCWTest() is called. Debug builds only.
     * @param freq_mhz Carrier frequency in MHz.
     * @retval True if the carrier was started successfully, false otherwise.
     */
    bool StartCWTest(uint32_t freq_mhz);

    /**
     * Stops a CW carrier started with StartCWTest() and resumes normal packet reception. Debug builds only.
     * @retval True if the carrier was stopped and Rx resumed successfully, false otherwise.
     */
    bool StopCWTest();

    /**
     * Retunes the synthesizer to the requested frequency and restarts packet RX so instantaneous RSSI
     * can be polled with ReadRssiDbm(). Suspends normal reception until StopRssiScan() is called.
     * Debug builds only.
     * @param freq_mhz RX frequency in MHz.
     * @retval True if the scan was started successfully, false otherwise.
     */
    bool StartRssiScan(uint32_t freq_mhz);

    /**
     * Reads the instantaneous RSSI from the RF core. Only valid while an RX command is actively
     * running (e.g. during a StartRssiScan()). Debug builds only.
     * @retval RSSI in dBm, or RF_GET_RSSI_ERROR_VAL (-128) if the RF core is not receiving.
     */
    int8_t ReadRssiDbm();

    /**
     * Stops an RSSI scan started with StartRssiScan() and resumes normal packet reception. Debug
     * builds only.
     * @retval True if normal reception was restored successfully, false otherwise.
     */
    bool StopRssiScan();
#endif

    bool rx_enabled = true;

    // Health / diagnostics counter, reported and reset via AT+RX_STATS. Incremented when the RX
    // command ends with an error status (e.g. PROP_ERROR_RXFULL/RXBUF) and has to be restarted.
    uint32_t rx_error_restart_count = 0;

private:
    SubGHzRadioConfig config_;

    RF_Handle rf_handle_;
    RF_Object rf_object_;

    rfc_dataEntryPartial_t *current_data_entry_; // Pointer to the data entry being processed (not held by the RF core).
    rfc_propRxOutput_t rx_statistics_;

    RF_CmdHandle rx_cmd_handle_;

    uint32_t last_rx_start_timestamp_ms_ = 0;
};

extern SubGHzRadio subg_radio;