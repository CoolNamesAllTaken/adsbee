#include <stdio.h>  // for printing

#include <cstring>   // for strcat
#include <iostream>  // for AT command ingestion

#include "comms.hh"
#include "main.hh"
#include "pico/stdlib.h"  // for getchar etc

// For mapping cpp_at_printf
#include <cstdarg>
// #include "printf.h" // for using custom printf defined in printf.h
#include <cstdio>  // for using regular printf

/** CppAT Printf Override **/
int CppAT::cpp_at_printf(const char *format, ...) {
    va_list args;
    va_start(args, format);
    int res = vprintf(format, args);
    va_end(args);
    return res;
}

/** AT Command Callback Functions **/

/**
 * AT+CONFIG Callback
 * AT+CONFIG=<config_mode:uint16_t>
 *  config_mode = 0 (print as normal), 1 (suppress non-configuration print messages)
 */
CPP_AT_CALLBACK(CommsManager::ATConfigCallback) {
    if (op == '?') {
        // AT+CONFIG mode query.
        CPP_AT_PRINTF("=%d", at_config_mode_);
        CPP_AT_SILENT_SUCCESS();
    } else if (op == '=') {
        // AT+CONFIG set command.
        if (!CPP_AT_HAS_ARG(0)) {
            CPP_AT_ERROR("Need to specify a config mode to run.")
        }
        ATConfigMode new_mode;
        CPP_AT_TRY_ARG2NUM(0, (uint16_t &)new_mode);
        if (new_mode >= ATConfigMode::kInvalid) {
            CPP_AT_ERROR("%d is not a valid config mode.", (uint16_t)new_mode);
        }

        at_config_mode_ = new_mode;
        CPP_AT_SUCCESS()
    }
    CPP_AT_ERROR();
}

/**
 * AT+MTLSET Callback
 * AT+MTLSET=<mtl_lo_mv>,<mtl_hi_mv>
 *  mtl_lo_mv = Low trigger value, mV.
 *  mtl_hi_mv = High trigger value, mV.
 * AT+MTLSET?
 * +MTLSET=
 */
CPP_AT_CALLBACK(CommsManager::ATMTLSetCallback) {
    if (op == '?') {
        // AT+MTLSET value query.
        CPP_AT_PRINTF("=%d,%d\r\n", ads_bee.GetMTLLoMilliVolts(), ads_bee.GetMTLHiMilliVolts());
        CPP_AT_SILENT_SUCCESS();
    } else if (op == '=') {
        // Attempt setting LO MTL value, in milliVolts, if first argument is not blank.
        if (CPP_AT_HAS_ARG(0)) {
            uint16_t new_mtl_lo_mv;
            CPP_AT_TRY_ARG2NUM(0, new_mtl_lo_mv);
            if (!ads_bee.SetMTLLoMilliVolts(new_mtl_lo_mv)) {
                CPP_AT_ERROR("Failed to set mtl_lo_mv.");
            }
        }
        // Attempt setting HI MTL value, in milliVolts, if second argument is not blank.
        if (CPP_AT_HAS_ARG(1)) {
            // Set HI MTL value, in milliVolts.
            uint16_t new_mtl_hi_mv;
            CPP_AT_TRY_ARG2NUM(1, new_mtl_hi_mv);
            if (!ads_bee.SetMTLHiMilliVolts(new_mtl_hi_mv)) {
                CPP_AT_ERROR("Failed to set mtl_hi_mv.");
            }
        }
        CPP_AT_SUCCESS();
    }
    CPP_AT_ERROR();
}

CPP_AT_CALLBACK(CommsManager::ATMTLReadCallback) {
    switch (op) {
        case '?':
            // Read command.
            CPP_AT_PRINTF("=%d,%d\r\n", ads_bee.ReadMTLLoMilliVolts(), ads_bee.ReadMTLHiMilliVolts());
            CPP_AT_SILENT_SUCCESS();
            break;
        default:
            CPP_AT_ERROR("Operator not supported.");
    }
    CPP_AT_ERROR();
}

CPP_AT_CALLBACK(CommsManager::ATRxGainCallback) {
    switch (op) {
        case '=':
            if (CPP_AT_HAS_ARG(0)) {
                int rx_gain;
                CPP_AT_TRY_ARG2NUM(0, rx_gain);
                if (!ads_bee.SetRxGain(rx_gain)) {
                    CPP_AT_ERROR("Failed while setting rx gain to %d.", rx_gain);
                }
                CPP_AT_SUCCESS();
            }
            CPP_AT_ERROR("Received operator '%c' but no args.", op);
            break;
        case '?':
            CPP_AT_PRINTF("=%d", ads_bee.ReadRxGain());
            CPP_AT_SILENT_SUCCESS();
            break;
        default:
            CPP_AT_ERROR("Operator '%c' not supported.", op);
    }
    CPP_AT_ERROR();
}

static const CppAT::ATCommandDef_t at_command_list[] = {
    {.command_buf = "+CONFIG",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf =
         "AT+CONFIG=<config_mode>\r\n\tSet whether the module is in CONFIG or RUN mode. RUN=0, CONFIG=1.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATConfigCallback, comms_manager)},
    {.command_buf = "+MTLSET",
     .min_args = 0,
     .max_args = 2,
     .help_string_buf = "AT+MTLSet=<mtl_lo_mv_>,<mtl_hi_mv_>\r\n\tQuery or set both HI and LO Minimum Trigger Level "
                        "(MTL) thresholds for RF power detector.\r\n"
                        "\tQuery is AT+MTLSET?, Set is AT+MTLSet=<mtl_lo_mv_>,<mtl_hi_mv_>.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATMTLSetCallback, comms_manager)},
    {.command_buf = "+MTLREAD",
     .min_args = 0,
     .max_args = 0,
     .help_string_buf =
         "Read ADC counts and mV values for high and low MTL thresholds. Call with no ops nor arguments, "
         "AT+MTLREAD.\r\n",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATMTLReadCallback, comms_manager)},
    {.command_buf = "+RXGAIN",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf = "Set value of Rx Gain Digipot.\r\n\t"
                        "AT+RXGAIN=<rx_gain>\r\n\tAT+RXGAIN?\r\n\t+RXGAIN=<rx_gain>.\r\n",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATRxGainCallback, comms_manager)

    }

};

CommsManager::CommsManager(CommsManagerConfig config_in)
    : config_(config_in),
      at_parser_(CppAT(at_command_list, sizeof(at_command_list) / sizeof(at_command_list[0]), true)),
      ads_bee_(config_in.ads_bee) {}

bool CommsManager::InitAT() {
    // Initialize AT command parser with statically allocated list of AT commands.

    return true;
}

bool CommsManager::UpdateAT() {
    static char at_command_buf[kATCommandBufMaxLen];
    // Check for new AT commands. Process up to one line per loop.
    int c = getchar_timeout_us(0);
    while (c != PICO_ERROR_TIMEOUT) {
        char buf[2] = {static_cast<char>(c), '\0'};
        strcat(at_command_buf, buf);
        if (c == '\n') {
            at_parser_.ParseMessage(std::string_view(at_command_buf));
            at_command_buf[0] = '\0';  // clear command buffer
        }
        c = getchar_timeout_us(0);
    }
    return true;
}