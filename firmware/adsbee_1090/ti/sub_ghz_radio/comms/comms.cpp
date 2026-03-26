#include "comms.hh"

#include <cstdarg>  // For debug printf.
#include <cstdio>   // Regular pico/stdio.h doesn't support vprint functions.

#include "spi_coprocessor.hh"

#define USE_LOG_MESSAGE_GUARD

CommsManager::CommsManager(CommsManagerConfig config_in) : config_(config_in) {}

bool CommsManager::Init() { return true; }

bool CommsManager::Update() { return true; }

bool CommsManager::LogMessageToCoprocessor(SettingsManager::LogLevel log_level, const char* tag, const char* format,
                                           ...) {
#ifdef USE_LOG_MESSAGE_GUARD
    // The log message guard is a total hack since we don't have a proper RTOS with pre-emption to enable printing from
    // multiple threads. The first context to try printing wins, everyone else gets nothing.
    static bool log_message_guard = false;
    if (log_message_guard) {
        return false;
    }
    log_message_guard = true;
#endif  // USE_LOG_MESSAGE_GUARD

    if (log_level > settings_manager.settings.log_level) {
#ifdef USE_LOG_MESSAGE_GUARD
        log_message_guard = false;  // Reset guard.
#endif                              // USE_LOG_MESSAGE_GUARD
        return true;                // Skip logging messages that aren't necessary.
    }
    va_list args;
    va_start(args, format);
    bool ret = pico.LogMessage(log_level, tag, format, args);
    va_end(args);
#ifdef USE_LOG_MESSAGE_GUARD
    log_message_guard = false;  // Reset guard.
#endif                          // USE_LOG_MESSAGE_GUARD
    return ret;
}