#ifndef COMMS_HH_
#define COMMS_HH_

#include <cstdio>

// Use do while(0) structure to enforce semicolon usage after macro.
#define CONSOLE_INFO(tag, format, ...)                                     \
    do {                                                                   \
        printf("INFO: " tag ": " format "\r\n" __VA_OPT__(, ) __VA_ARGS__) \
    } while (0)
#define CONSOLE_WARNING(tag, format, ...)                                     \
    do {                                                                      \
        printf("WARNING: " tag ": " format "\r\n" __VA_OPT__(, ) __VA_ARGS__) \
    } while (0)
#define CONSOLE_ERROR(tag, format, ...)                                     \
    do {                                                                    \
        printf("ERROR: " tag ": " format "\r\n" __VA_OPT__(, ) __VA_ARGS__) \
    } while (0)

#endif /* COMMS_HH_ */