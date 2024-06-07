#ifndef COMMS_HH_
#define COMMS_HH_

#include <cstdio>

#define CONSOLE_LOG(format, ...) \
    printf("LOG: " format __VA_OPT__(, ) __VA_ARGS__);
#define CONSOLE_WARNING(format, ...) \
    printf("WARNING: " format __VA_OPT__(, ) __VA_ARGS__);
#define CONSOLE_ERROR(format, ...) \
    printf("ERROR: " format __VA_OPT__(, ) __VA_ARGS__);

#endif /* COMMS_HH_ */