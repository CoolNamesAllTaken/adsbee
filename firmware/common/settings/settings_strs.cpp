#include "settings.hh"

// These strings are initialized here since they can't be initialized in settings.hh because they are static.
// The ESP32 and RP2040 have separate settings.cpp files, but want to share these static string definitions.
const char SettingsManager::kConsoleLogLevelStrs[SettingsManager::LogLevel::kNumLogLevels]
                                                [SettingsManager::kConsoleLogLevelStrMaxLen] = {"SILENT", "ERRORS",
                                                                                                "WARNINGS", "INFO"};
const char SettingsManager::kSerialInterfaceStrs[SettingsManager::SerialInterface::kNumSerialInterfaces]
                                                [SettingsManager::kSerialInterfaceStrMaxLen] = {"CONSOLE", "COMMS_UART",
                                                                                                "GNSS_UART"};
const char SettingsManager::kReportingProtocolStrs[SettingsManager::ReportingProtocol::kNumProtocols]
                                                  [SettingsManager::kReportingProtocolStrMaxLen] = {
                                                      "NONE",  "RAW",      "BEAST",    "BEAST_RAW",
                                                      "CSBEE", "MAVLINK1", "MAVLINK2", "GDL90"};

const char SettingsManager::kSubGHzModeStrs[SettingsManager::kNumSubGHzRadioModes]
                                           [SettingsManager::kSubGHzModeStrMaxLen] = {
                                               "UAT_RX",  // UAT mode (978MHz receiver).
};