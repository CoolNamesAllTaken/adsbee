#ifndef COMMS_HH_
#define COMMS_HH_

#include <cstring>

#include "stdio.h"  // for printing

#define TEXT_COLOR_RED                 "\033[31m"
#define TEXT_COLOR_GREEN               "\033[32m"
#define TEXT_COLOR_YELLOW              "\033[33m" /* orange on some systems */
#define TEXT_COLOR_BLUE                "\033[34m"
#define TEXT_COLOR_MAGENTA             "\033[35m"
#define TEXT_COLOR_CYAN                "\033[36m"
#define TEXT_COLOR_LIGHT_GRAY          "\033[37m"
#define TEXT_COLOR_DARK_GRAY           "\033[90m"
#define TEXT_COLOR_BRIGHT_RED          "\033[91m"
#define TEXT_COLOR_BRIGHT_GREEN        "\033[92m"
#define TEXT_COLOR_BRIGHT_YELLOW       "\033[93m"
#define TEXT_COLOR_BRIGHT_BLUE         "\033[94m"
#define TEXT_COLOR_BRIGHT_MAGENTA      "\033[95m"
#define TEXT_COLOR_BRIGHT_CYAN         "\033[96m"
#define TEXT_COLOR_WHITE               "\033[97m"

#define TEXT_COLOR_RESET               "\033[0m"

#define CONSOLE_PRINTF(format, ...)    printf(format __VA_OPT__(, ) __VA_ARGS__);
#define CONSOLE_INFO(tag, format, ...) printf(tag ": " format "\r\n" __VA_OPT__(, ) __VA_ARGS__);
#define CONSOLE_WARNING(tag, format, ...) \
    printf(tag ": " TEXT_COLOR_YELLOW format TEXT_COLOR_RESET "\r\n" __VA_OPT__(, ) __VA_ARGS__);
#define CONSOLE_ERROR(tag, format, ...) \
    printf(tag ": " TEXT_COLOR_RED format TEXT_COLOR_RESET "\r\n" __VA_OPT__(, ) __VA_ARGS__);

#endif /* COMMS_HH_ */