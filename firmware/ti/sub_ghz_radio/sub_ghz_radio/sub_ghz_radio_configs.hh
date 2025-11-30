#include "smartrf/smartrf_settings.h"
#include "sub_ghz_radio.hh"

extern "C" {
/* clang-format off */
#include DeviceFamily_constructPath(rf_patches/rf_patch_cpe_prop.h)
#include DeviceFamily_constructPath(rf_patches/rf_patch_rfe_genook.h)
#include DeviceFamily_constructPath(rf_patches/rf_patch_mce_genook.h)
#include DeviceFamily_constructPath(inc/hw_rfc_dbell.h)
/* clang-format on */
}

static uint32_t pUATOverrides[] = {
    // override_prop_common.xml
    // DC/DC regulator: In Tx, use DCDCCTL5[3:0]=0x7 (DITHER_EN=0 and IPEAK=7).
    (uint32_t)0x00F788D3,
    // override_prop_common_sub1g.xml
    // Set RF_FSCA.ANADIV.DIV_SEL_BIAS = 1. Bits [0:16, 24, 30] are don't care..
    (uint32_t)0x4001405D,
    // Set RF_FSCA.ANADIV.DIV_SEL_BIAS = 1. Bits [0:16, 24, 30] are don't care..
    (uint32_t)0x08141131,
    // override_tc782_tc783.xml
    // Tx: Configure PA ramp time, PACTL2.RC=0x3 (in ADI0, set PACTL2[4:3]=0x3)
    ADI_2HALFREG_OVERRIDE(0, 16, 0x8, 0x8, 17, 0x1, 0x1),
    // Rx: Set AGC reference level to 0x2E (default: 0x2E)
    HW_REG_OVERRIDE(0x609C, 0x002E),
    // Rx: Set RSSI offset to adjust reported RSSI by -4 dB (default: -2), trimmed for external bias and differential
    // configuration
    (uint32_t)0x000488A3,
    // Rx: Set LNA Ib boost
    ADI_HALFREG_OVERRIDE(0, 5, 0xF, 0x2),
    // Rx: Set anti-aliasing filter bandwidth to 0x0 (in ADI0, set IFAMPCTL3[7:4]=0xD)
    ADI_HALFREG_OVERRIDE(0, 61, 0xF, 0x0),
    // TX: Reduce analog ramping wait time
    HW_REG_OVERRIDE(0x6028, 0x001A),
    // TX: set intFreq = 0
    (uint32_t)0x00000343, (uint32_t)0xFFFFFFFF};

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
         .pRegOverride = pUATOverrides,
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
            // (e.g. SPI). This leads to the RF core writing infinitely into memory, causing a non-deterministic crash
            // behavior. Make sure the software interrupt priority for the RF system is higher than the software
            // interrupt priority for SPI (I set hardware interrupt priority higher too, but that doesn't seem to fix it
            // on its own). Setting RF software interrupt priority 1 point higher than SPI interrupt priority seems to
            // work well. Higher values for RF software interrupt priority lead to crashes. To sidestep this drama, just
            // set the max expected packet length as  maxPktLen and take the performance hit (more rx airtime wasted per
            // packet received).
            .maxPktLen = RawUATUplinkPacket::kUplinkMessageNumBytes,  // 0 = unlimited / unknown length packet mode
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

// Overrides for CMD_PROP_RADIO_DIV_SETUP
static uint32_t pModeSOverrides[] = {
    // override_tc597.xml
    // PHY: Use MCE RAM patch (mode 0), RFE RAM patch (mode 0)
    MCE_RFE_OVERRIDE(1, 0, 0, 1, 0, 0),
    // MCE_RFE_OVERRIDE(1, 0, 17, 1, 0, 0),  // Enable manchester for payload and CRC.
    // Tx: Configure PA ramp time, PACTL2.RC=0x3 (in ADI0, set PACTL2[4:3]=0x3)
    ADI_2HALFREG_OVERRIDE(0, 16, 0x8, 0x8, 17, 0x1, 0x1),
    // Rx: Set AGC reference level to 0x19 (default: 0x2E)
    HW_REG_OVERRIDE(0x609C, 0x0019),
    // Rx: Set RSSI offset to adjust reported RSSI by 4 dB (default: -2), trimmed for external bias and differential
    // configuration
    (uint32_t)0x00FB88A3,
    // Rx: Set anti-aliasing filter bandwidth to 0xD (in ADI0, set IFAMPCTL3[7:4]=0xD)
    ADI_HALFREG_OVERRIDE(0, 61, 0xF, 0xF),
    // TX: Set FSCA divider bias to 1
    HW32_ARRAY_OVERRIDE(0x405C, 1),
    // TX: Set FSCA divider bias to 1
    (uint32_t)0x08141131,
    // OOK: Set duty cycle to compensate for PA ramping
    HW_REG_OVERRIDE(0x51E4, 0x80AF),
    // Set code length k=7 in viterbi
    HW_REG_OVERRIDE(0x5270, 0x0002),
    // Tx: Configure PA ramping, set wait time before turning off (0x1A ticks of 16/24 us = 17.3 us).
    HW_REG_OVERRIDE(0x6028, 0x001A),
    // override_prop_common_sub1g.xml
    // Set RF_FSCA.ANADIV.DIV_SEL_BIAS = 1. Bits [0:16, 24, 30] are don't care..
    (uint32_t)0x4001405D,
    // Set RF_FSCA.ANADIV.DIV_SEL_BIAS = 1. Bits [0:16, 24, 30] are don't care..
    (uint32_t)0x08141131,
    // override_prop_common.xml
    // DC/DC regulator: In Tx, use DCDCCTL5[3:0]=0x7 (DITHER_EN=0 and IPEAK=7).
    (uint32_t)0x00F788D3,

    // Custom overrides by John.
    // Route RAT_GPO1 (Sync word detected) to RFC_GPO0
    HW_REG_OVERRIDE(0x1110, RFC_DBELL_SYSGPOCTL_GPOCTL0_RATGPO1),
    // Additional override for sync word GPIO, as per
    // https://dev.ti.com/tirex/content/simplelink_cc13xx_cc26xx_sdk_8_30_01_01/docs/proprietary-rf/proprietary-rf-users-guide/rf-core/signal-routing.html#sec-read-rat-gpo1.
    (uint32_t)0x008F88B3,

    // End of overrides.
    (uint32_t)0xFFFFFFFF};

static const SubGHzRadio::SubGHzRadioConfig kModeSRxConfig = {
    // TI-RTOS RF Mode Object
    .RF_prop = {.rfMode = RF_MODE_AUTO,
                .cpePatchFxn = &rf_patch_cpe_prop,
                .mcePatchFxn = &rf_patch_mce_genook,
                .rfePatchFxn = &rf_patch_rfe_genook},

    // Proprietary Mode Radio Setup Command for all frequency bands.
    .RF_cmdPropRadioDivSetup = {.commandNo = 0x3807,
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
                                        .modType = 0x2,  // OOK
                                        .deviation = 0x0,
                                        .deviationStepSz = 0x0,
                                    },
                                .symbolRate =
                                    {
                                        .preScale = 0xF,
                                        .rateWord = 0x140000,  // 2 Mbps
                                        .decimMode = 0x0,
                                    },
                                .rxBw = 0x67,  // 3767.4 kHz
                                .preamConf =
                                    {
                                        .nPreamBytes = 0x0,
                                        .preamMode = 0x0,
                                    },
                                .formatConf =
                                    {
                                        .nSwBits = 16,  // Mode S preamble at 2Mbps is 16 bits (8us) long.
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
                                .pRegOverride = pModeSOverrides,
                                .centerFreq = 0x0442,        // 1090MHz
                                .intFreq = (int16_t)0x8000,  // Use default IF.
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
                 .frequency = 0x0442,
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
            .syncWord0 = (uint32_t)(0b1010000101000000 << 16),
            .syncWord1 = (uint32_t)(0x1010000101000000 << 16),
            // This needs to be set to 0, or else the length can't be overridden dynamically.
            // WARNING: Setting packet length via the RF command callback can get stomped by another interrupt context
            // (e.g. SPI). This leads to the RF core writing infinitely into memory, causing a non-deterministic crash
            // behavior. Make sure the software interrupt priority for the RF system is higher than the software
            // interrupt priority for SPI (I set hardware interrupt priority higher too, but that doesn't seem to fix it
            // on its own). Setting RF software interrupt priority 1 point higher than SPI interrupt priority seems to
            // work well. Higher values for RF software interrupt priority lead to crashes. To sidestep this drama, just
            // set the max expected packet length as  maxPktLen and take the performance hit (more rx airtime wasted per
            // packet received).
            .maxPktLen =
                2 * RawModeSPacket::kExtendedSquitterPacketLenBytes,  // 0 = unlimited / unknown length packet mode
            // The last 4 bits of the Sync word are interpreted as the header, so the rest of the packet stays
            // byte-aligned.
            .hdrConf =
                {
                    .numHdrBits = 0x0,
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

static const SubGHzRadio::SubGHzRadioConfig* kSubGRadioConfigs[SettingsManager::SubGMode::kNumSubGModes] = {
    &kUATRxConfig,   /* kSubGHzRadioModeUATRx */
    &kModeSRxConfig, /* kSubGHzRadioModeModeSRx */
};