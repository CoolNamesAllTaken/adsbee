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
    static const uint16_t kRxPacketQueueLen = 4;
    static const uint16_t kRxPacketMaxLenBytes = RawUATUplinkPacket::kUplinkMessageLenBytes + 1; // +1 to account for last byte of sync word.

    struct SubGHzRadioConfig
    {
        // Add any configuration parameters needed for the SubGHzRadio.
    };

    SubGHzRadio(SubGHzRadioConfig config_in): config_(config_in) {};
    ~SubGHzRadio() {};

    bool Init();
    void Deinit();

    bool Update();

    bool HandlePacketRx();

private:
    SubGHzRadioConfig config_;

    RF_Handle rf_handle_;
    RF_Object rf_object_;

    rfc_dataEntryPartial_t *current_data_entry_; // Pointer to the data entry being processed (not held by the RF core).
    rfc_propRxOutput_t rx_statistics_;
};

extern SubGHzRadio subg_radio;