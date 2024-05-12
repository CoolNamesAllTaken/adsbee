#include "main.hh"
#include "comms.hh"

#include "pico/stdlib.h" // for getchar etc
#include <stdio.h>  // for printing
#include <iostream> // for AT command ingestion
#include <cstring> // for strcat

// For mapping cpp_at_printf
#include <cstdarg>
// #include "printf.h" // for using custom printf defined in printf.h
#include <cstdio> // for using regular printf

/** Constants **/
static const uint16_t kATCommandBufMaxLen = 1000;

/** Enums **/
typedef enum {
    RUN = 0,
    CONFIG = 1
} ATConfigMode_t;

/** Global Variables **/
extern ADSBee ads_bee;
ATConfigMode_t at_config_mode = RUN;

/** CppAT Printf Override **/
int CppAT::cpp_at_printf(const char *format, ...)
{
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
CPP_AT_CALLBACK(ATConfigCallback)
{
    if (op == '?')
    {
        // AT+CONFIG mode query.
        printf("AT+CONFIG=%d", at_config_mode);
    }
    else if (op == '=')
    {
        // AT+CONFIG set command.
        if (num_args != 1)
        {
            printf("ERROR: Incorrect number of args.\r\n");
            return false;
        }
        ATConfigMode_t new_mode;
        CPP_AT_TRY_ARG2NUM(0, (uint16_t &)new_mode);

        at_config_mode_ = new_mode;
        printf("OK\r\n");
    }
    return true;
}

/**
 * AT+MTLSET Callback
 * AT+MTLSET=<mtl_lo_mv>,<mtl_hi_mv>
 *  mtl_lo_mv = Low trigger value, mV.
 *  mtl_hi_mv = High trigger value, mV.
 * AT+MTLSET?
 * +MTLSET=
 */
CPP_AT_CALLBACK(ATMTLSetCallback)
{
    if (op == '?')
    {
        // AT+MTLSET value query.
        CPP_AT_PRINTF("=%d,%d\r\n", ads_bee.GetMTLLoMilliVolts(), ads_bee.GetMTLHiMilliVolts());
    }
    else if (op == '=')
    {
        // Attempt setting LO MTL value, in milliVolts, if first argument is not blank.
        if (CPP_AT_HAS_ARG(0))
        {
            uint16_t new_mtl_lo_mv;
            CPP_AT_TRY_ARG2NUM(0, new_mtl_lo_mv);
            if (!ads_bee.SetMTLLoMilliVolts(new_mtl_lo_mv))
                CPP_AT_ERROR("Failed to set mtl_lo_mv.");
        }
        // Attempt setting HI MTL value, in milliVolts, if second argument is not blank.
        if (CPP_AT_HAS_ARG(1))
        {
            // Set HI MTL value, in milliVolts.
            uint16_t new_mtl_hi_mv;
            CPP_AT_TRY_ARG2NUM(1, new_mtl_hi_mv);
            if (!ads_bee.SetMTLHiMilliVolts(new_mtl_hi_mv))
                CPP_AT_ERROR("Failed to set mtl_hi_mv.");
        }
        CPP_AT_SUCCESS();
    }
    return true;
}

CPP_AT_CALLBACK(ATMTLReadCallback)
{
    switch (op)
    {
    case '?':
        // Read command.
        CPP_AT_PRINTF("=%d,%d\r\n", ads_bee.ReadMTLLoMilliVolts(), ads_bee.ReadMTLHiMilliVolts());
        break;
    default:
        CPP_AT_ERROR("Operator not supported.");
    }

    return true;
}

static const CppAT::ATCommandDef_t at_command_list[] = {
    {.command_buf = "+CONFIG",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf = "AT+CONFIG=<config_mode>\r\n\tSet whether the module is in CONFIG or RUN mode. RUN=0, CONFIG=1.",
     .callback = ATConfigCallback},
    {.command_buf = "+MTLSET",
     .min_args = 0,
     .max_args = 2,
     .help_string_buf = "AT+MTLSet=<mtl_lo_mv_>,<mtl_hi_mv_>\r\n\tQuery or set both HI and LO Minimum Trigger Level (MTL) thresholds for RF power detector.\r\n"
                        "\tQuery is AT+MTLSET?, Set is AT+MTLSet=<mtl_lo_mv_>,<mtl_hi_mv_>.",
     .callback = ATMTLSetCallback},
    {.command_buf = "+MTLREAD",
     .min_args = 0,
     .max_args = 0,
     .help_string_buf = "Read ADC counts and mV values for high and low MTL thresholds. Call with no ops nor arguments, "
                        "AT+MTLREAD.\r\n",
     .callback = ATMTLReadCallback}};

CppAT at_parser = CppAT(
    at_command_list,
    sizeof(at_command_list) / sizeof(at_command_list[0]),
    true);

bool InitCommsAT()
{
    // Initialize AT command parser with statically allocated list of AT commands.
    return true;
}

bool UpdateCommsAT()
{
    static char at_command_buf[kATCommandBufMaxLen];
    // Check for new AT commands. Process up to one line per loop.
    int c = getchar_timeout_us(0);
    while (c != PICO_ERROR_TIMEOUT)
    {
        char buf[2] = {static_cast<char>(c), '\0'};
        strcat(at_command_buf, buf);
        if (c == '\n')
        {
            at_parser.ParseMessage(std::string_view(at_command_buf));
            at_command_buf[0] = '\0'; // clear command buffer
        }
        c = getchar_timeout_us(0);
    }
}