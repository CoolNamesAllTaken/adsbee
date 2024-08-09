#ifndef COMMS_HH_
#define COMMS_HH_

#include <cstdio>

// Use do while(0) structure to enforce semicolon usage after macro.
#define CONSOLE_INFO(tag, format, ...)    printf("INFO: " tag ": " format "\r\n" __VA_OPT__(, ) __VA_ARGS__)
#define CONSOLE_WARNING(tag, format, ...) printf("WARNING: " tag ": " format "\r\n" __VA_OPT__(, ) __VA_ARGS__)
#define CONSOLE_ERROR(tag, format, ...)   printf("ERROR: " tag ": " format "\r\n" __VA_OPT__(, ) __VA_ARGS__)

#endif /* COMMS_HH_ */