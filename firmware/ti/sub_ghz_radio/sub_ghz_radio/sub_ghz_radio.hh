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
#include "RFQueue.hh"

class SubGHzRadio
{
public:
    static const uint16_t kRxPacketQueueLen = 2;
    static const uint16_t kRxPacketMaxLenBytes = 272 / kBitsPerByte; // 34 bytes (long UAT packet).
    static const uint16_t kRxPacketNumAppendedBytes = 2; // 1 header byte + 1 status byte.

    struct SubGHzRadioConfig
    {
        // Add any configuration parameters needed for the SubGHzRadio.
    };

    SubGHzRadio(SubGHzRadioConfig config_in): config_(config_in) {};
    ~SubGHzRadio() {};

    bool Init();
    void Deinit();

private:
    SubGHzRadioConfig config_;

    RF_Handle rf_handle_;
    RF_Object rf_object_;
    dataQueue_t data_queue_;

    uint8_t rx_data_entry_buffer_[RF_QUEUE_DATA_ENTRY_BUFFER_SIZE(kRxPacketQueueLen, kRxPacketMaxLenBytes, kRxPacketNumAppendedBytes)]; // Buffer for receiving data entries.
};