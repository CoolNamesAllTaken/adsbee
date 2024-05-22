#include "comms.hh"

#include <cstdarg>  // For debug printf.
#include <cstdio>   // For debug printf.

bool CommsManager::Init() {
    InitAT();
    return true;
}

bool CommsManager::Update() {
    UpdateAT();
    return true;
}

int CommsManager::debug_printf(const char *format, ...) {
    if (at_config_mode_ == ATConfigMode::kConfig) return 0;
    va_list args;
    va_start(args, format);
    int res = vprintf(format, args);
    va_end(args);
    return res;
}