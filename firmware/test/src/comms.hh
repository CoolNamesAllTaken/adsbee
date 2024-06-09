#ifndef COMMS_HH_
#define COMMS_HH_

#include <cstdio>

#define CONSOLE_LOG(format, ...) \
    printf("LOG: " format "\r\n" __VA_OPT__(, ) __VA_ARGS__);
#define CONSOLE_WARNING(format, ...) \
    printf("WARNING: " format "\r\n" __VA_OPT__(, ) __VA_ARGS__);
#define CONSOLE_ERROR(format, ...) \
    printf("ERROR: " format "\r\n" __VA_OPT__(, ) __VA_ARGS__);

#endif /* COMMS_HH_ */