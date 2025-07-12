#include "comms.hh"

#include <cstdarg> // For debug printf.
#include <cstdio>  // Regular pico/stdio.h doesn't support vprint functions.

#include "spi_coprocessor.hh"

CommsManager::CommsManager(CommsManagerConfig config_in)
    : config_(config_in) {}

bool CommsManager::Init()
{
    return true;
}

bool CommsManager::Update()
{
    return true;
}

bool CommsManager::LogMessageToCoprocessor(SettingsManager::LogLevel log_level, const char *tag, const char *format,
                                           ...)
{
    return true; // FIXME: remove this.
    if (log_level > settings_manager.settings.log_level)
    {
        return true; // Skip logging messages that aren't necessary.
    }
    va_list args;
    va_start(args, format);
    bool ret = pico.LogMessage(log_level, tag, format, args);
    va_end(args);
    return ret;
}