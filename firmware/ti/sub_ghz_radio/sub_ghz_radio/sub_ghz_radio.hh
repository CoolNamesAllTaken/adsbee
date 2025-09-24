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
    static const uint16_t kRxPacketQueueLen = 2;
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
        // Bias tee is active LO because it's a PMOS device.
        CONSOLE_INFO("SubGHzRadio::SetBiasTeeEnable", "Bias tee %s", enabled ? "ENABLED" : "DISABLED");
        GPIO_write(bsp.kSubGBiasTeeEnablePin, !enabled);
    }
    bool StartPacketRx();
    bool Update();

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