#pragma once

extern "C" {
#include <ti/drivers/GPIO.h>
#include <ti/drivers/rf/RF.h>
#include <ti_radio_config.h>

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
#include "mode_s_packet.hh"

class SubGHzRadio
{
public:
    static const uint16_t kRxPacketQueueLen = 2;

    // This packet length is used for sizing partial data entry payloads. Set it to the maximum packet length across all protocols that can be received.
    static const uint16_t kRxPacketMaxLenBytes = RawUATUplinkPacket::kUplinkMessageNumBytes;

    struct SubGHzRadioConfig
    {
        RF_Mode RF_prop;
        rfc_CMD_PROP_RADIO_DIV_SETUP_t RF_cmdPropRadioDivSetup;
        rfc_CMD_FS_t RF_cmdFs;
        rfc_CMD_PROP_RX_ADV_t RF_cmdPropRxAdv;
    };

    SubGHzRadio(SubGHzRadioConfig *config_in) {
        SetConfig(config_in);
    };
    SubGHzRadio() {
        // Default constructor: don't copy in a config yet.
    }
    ~SubGHzRadio() {};

    void SetConfig(const SubGHzRadioConfig *config) {
        memcpy(&config_, config, sizeof(SubGHzRadioConfig));
    }

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
        // Bias tee is active LO because it's a PMOS device.
        CONSOLE_INFO("SubGHzRadio::SetBiasTeeEnable", "Bias tee %s", enabled ? "ENABLED" : "DISABLED");
        GPIO_write(bsp.kSubGBiasTeeEnablePin, !enabled);
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
     * Handles a received packet from the RF core.
     * @param filled_entry Pointer to the filled data entry from the RF core.
     * @retval True if packet was handled successfully, false otherwise.
     */
    bool HandlePacketRx(rfc_dataEntryPartial_t *filled_entry);

    bool rx_enabled = true;

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