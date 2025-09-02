#pragma once

extern "C"
{
#include <ti/drivers/rf/RF.h>
#include <ti/drivers/GPIO.h>
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
    static const uint16_t kRxPacketMaxLenBytes = RawUATUplinkPacket::kUplinkMessageLenBytes + 1; // +1 to account for last byte of sync word.

    struct SubGHzRadioConfig
    {
        // Add any configuration parameters needed for the SubGHzRadio.
    };

    SubGHzRadio(SubGHzRadioConfig config_in): config_(config_in) {};
    ~SubGHzRadio() {};

    bool Init();
    bool DeInit();
    void Deinit();

    bool StartPacketRx();
    bool Update();

    bool HandlePacketRx(rfc_dataEntryPartial_t *filled_entry);

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