#include "sub_ghz_radio.hh"
#include "pico.hh" // For LED blinks.

static void rf_cmd_complete_callback(RF_Handle h, RF_CmdHandle ch, RF_EventMask e)
{
    CONSOLE_INFO("SubGHzRadio", "RF command completed with handle %p, command handle %d, event mask %u", h, ch, e);
    if (e & RF_EventRxEntryDone)
    {
        pico_ll.BlinkSubGLED();
        CONSOLE_INFO("SubGHzRadio", "Received a new packet.");
        // Handle the received packet here.
    }
    RF_postCmd(h, (RF_Op *)&RF_cmdPropRx, RF_PriorityNormal, rf_cmd_complete_callback, RF_EventRxEntryDone);
}

bool SubGHzRadio::Init()
{
    RF_Params rf_params;
    RF_Params_init(&rf_params);

    if (RFQueue_defineQueue(&data_queue_,
                            rx_data_entry_buffer_,
                            sizeof(rx_data_entry_buffer_),
                            kRxPacketQueueLen,
                            kRxPacketMaxLenBytes + kRxPacketNumAppendedBytes))
    {
        CONSOLE_ERROR("SubGHzRadio::Init", "Failed to allocate space for all data entries.");
        return false; // Failed to allocate space for all data entries.
    }

    // All other RF_cmdPropRx settings are from smartrf/smartrf_settings.h.
    RF_cmdPropRx.pQueue = &data_queue_;

    rf_handle_ = RF_open(&rf_object_, &RF_prop, (RF_RadioSetup *)&RF_cmdPropRadioDivSetup, &rf_params);
    if (!rf_handle_)
    {
        CONSOLE_ERROR("SubGHzRadio::Init", "Failed to open RF device.");
        return false; // Failed to open RF handle.
    }

    RF_EventMask ret = RF_runCmd(rf_handle_, (RF_Op *)&RF_cmdFs, RF_PriorityNormal, nullptr, 0);
    if (ret != RF_EventLastCmdDone)
    {
        CONSOLE_ERROR("SubGHzRadio::Init", "Failed to set frequency.");
        RF_close(rf_handle_);
        return false; // Failed to run command FS.
    }

    RF_CmdHandle cmd = RF_postCmd(rf_handle_, (RF_Op *)&RF_cmdPropRx, RF_PriorityNormal, rf_cmd_complete_callback, RF_EventRxEntryDone);
    if (cmd < 0)
    {
        CONSOLE_ERROR("SubGHzRadio::Init", "Failed to post command PROP_RX: returned code %d.", cmd);
        RF_close(rf_handle_);
        return false; // Failed to post command PROP_RX.
    }
    return true;
}