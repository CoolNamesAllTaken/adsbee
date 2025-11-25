#include "smartrf/smartrf_settings.h"
#include "sub_ghz_radio.hh"

static const SubGHzRadio::SubGHzRadioConfig kUATRxConfig = {
    // TI-RTOS RF Mode Object
    .RF_prop = RF_prop,
    // Proprietary Mode Radio Setup Command for all frequency bands.
    .RF_cmdPropRadioDivSetup =
        {.commandNo = 0x3807,
         .status = 0x0000,
         .pNextOp = 0,  // INSERT APPLICABLE POINTER: (uint8_t*)&xxx
         .startTime = 0x00000000,
         .startTrigger =
             {
                 .triggerType = 0x0,
                 .bEnaCmd = 0x0,
                 .triggerNo = 0x0,
                 .pastTrig = 0x0,
             },
         .condition =
             {
                 .rule = 0x1,
                 .nSkip = 0x0,
             },
         .modulation =
             {
                 .modType = 0x1,
                 .deviation = 0x4E2,
                 .deviationStepSz = 0x0,
             },
         .symbolRate =
             {
                 .preScale = 0xF,
                 .rateWord = 0xA6BFB,
                 .decimMode = 0x0,
             },
         .rxBw = 0x64,
         .preamConf =
             {
                 .nPreamBytes = 0x0,
                 .preamMode = 0x0,
             },
         // Use a 32-bit sync word to allow the last 4 bits of the sync to be used for format discrimination.
         .formatConf =
             {
                 .nSwBits = 32,
                 .bBitReversal = 0x0,
                 .bMsbFirst = 0x1,
                 .fecMode = 0x0,
                 .whitenMode = 0x0,
             },
         .config =
             {
                 .frontEndMode = 0x0,
                 .biasMode = 0x1,
                 .analogCfgMode = 0x0,
                 .bNoFsPowerUp = 0x0,
                 .bSynthNarrowBand = 0x0,
             },
         .txPower = 0x003F,
         .pRegOverride = pOverrides,
         .centerFreq = 0x03D2,
         .intFreq = 0x0D99,
         .loDivider = 0x05},

    // Frequency synthesizer programming command.
    .RF_cmdFs = {.commandNo = 0x0803,
                 .status = 0x0000,
                 .pNextOp = 0,  // INSERT APPLICABLE POINTER: (uint8_t*)&xxx
                 .startTime = 0x00000000,
                 .startTrigger =
                     {
                         .triggerType = 0x0,
                         .bEnaCmd = 0x0,
                         .triggerNo = 0x0,
                         .pastTrig = 0x0,
                     },
                 .condition =
                     {
                         .rule = 0x1,
                         .nSkip = 0x0,
                     },
                 .frequency = 0x03D2,
                 .fractFreq = 0x0000,
                 .synthConf =
                     {
                         .bTxMode = 0x0,
                         .refFreq = 0x0,
                     },
                 .__dummy0 = 0x00,
                 .__dummy1 = 0x00,
                 .__dummy2 = 0x00,
                 .__dummy3 = 0x0000},

    // Proprietary RF advanced RX command.
    .RF_cmdPropRxAdv =
        {
            .commandNo = 0x3804,
            .status = 0x0000,
            .pNextOp = 0,  // INSERT APPLICABLE POINTER: (uint8_t*)&xxx
            .startTime = 0x00000000,
            .startTrigger =
                {
                    .triggerType = 0x0,
                    .bEnaCmd = 0x0,
                    .triggerNo = 0x0,
                    .pastTrig = 0x0,
                },
            .condition =
                {
                    .rule = 0x1,
                    .nSkip = 0x0,
                },
            .pktConf =
                {
                    .bFsOff = 0x0,
                    .bRepeatOk = 0x0,
                    .bRepeatNok = 0x0,
                    .bUseCrc = 0x0,
                    .bCrcIncSw = 0x0,
                    .bCrcIncHdr = 0x0,
                    .endType = 0x0,
                    .filterOp = 0x0,
                },
            .rxConf =
                {

                    .bAutoFlushIgnored = 0x0,
                    .bAutoFlushCrcErr = 0x0,
                    .bIncludeHdr = 0x1,
                    .bIncludeCrc = 0x1,
                    .bAppendRssi = 0x1,
                    .bAppendTimestamp = 0x1,
                    .bAppendStatus = 0x1,
                },
            // Sync on the most significant 32 bits of the 36 bit sync word. Save the last 4 bits of sync for
            // discrimination
            // between uplink and ADSB packets in the payload.
            .syncWord0 = RawUATADSBPacket::kSyncWordMS32,
            .syncWord1 = RawUATUplinkPacket::kSyncWordMS32,
            // This needs to be set to 0, or else the length can't be overridden dynamically.
            // WARNING: Setting packet length via the RF command callback can get stomped by another interrupt context
            // (e.g.
            // SPI). This leads to the RF core writing infinitely into memory, causing a non-deterministic crash
            // behavior.
            // Make sure the software interrupt priority for the RF system is higher than the software interrupt
            // priority
            // for SPI (I set hardware interrupt priority higher too, but that doesn't seem to fix it on its own).
            // Setting
            // RF software interrupt priority 1 point higher than SPI interrupt priority seems to work well. Higher
            // values
            // for RF software interrupt priority lead to crashes. To sidestep this drama, just set the max expected
            // packet
            // length as  maxPktLen and take the performance hit (more rx airtime wasted per packet received).
            .maxPktLen = SubGHzRadio::kRxPacketMaxLenBytes,  // 0 = unlimited / unknown length packet mode
            // The last 4 bits of the Sync word are interpreted as the header, so the rest of the packet stays
            // byte-aligned.
            .hdrConf =
                {
                    .numHdrBits = 0x4,
                    .lenPos = 0x0,
                    .numLenBits = 0x0,
                },

            .addrConf = {0},  // No address field.
            .lenOffset = 0x00,
            .endTrigger =
                {
                    .triggerType = 0x0,
                    .bEnaCmd = 0x0,
                    .triggerNo = 0x0,
                    .pastTrig = 0x0,
                },
            .endTime = 0x00000000,
            .pAddr = 0,   // INSERT APPLICABLE POINTER: (uint8_t*)&xxx
            .pQueue = 0,  // INSERT APPLICABLE POINTER: (dataQueue_t*)&xxx
            .pOutput = 0  // INSERT APPLICABLE POINTER: (uint8_t*)&xxx
        },
};

static const SubGHzRadio::SubGHzRadioConfig kModeSRxConfig = {
    // TI-RTOS RF Mode Object
    .RF_prop = RF_prop,

    // Proprietary Mode Radio Setup Command for all frequency bands.
    .RF_cmdPropRadioDivSetup = RF_cmdPropRadioDivSetup,

    // Frequency synthesizer programming command.
    .RF_cmdFs = RF_cmdFs,

    // Proprietary RF advanced RX command.
    .RF_cmdPropRxAdv = RF_cmdPropRxAdv,
};

static const SubGHzRadio::SubGHzRadioConfig*
    kSubGHzRadioConfigs[SettingsManager::SubGHzRadioMode::kNumSubGHzRadioModes] = {
        &kUATRxConfig,   /* kSubGHzRadioModeUATRx */
        &kModeSRxConfig, /* kSubGHzRadioModeModeSRx */
};