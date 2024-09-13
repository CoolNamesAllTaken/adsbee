#include "main.hh"

#include "comms.hh"  // For comms manager required by ADSBPacket for error reporting.
#include "gtest/gtest.h"
#include "settings.hh"

// CommsManager comms_manager = CommsManager({});
SettingsManager settings_manager = SettingsManager();

int main(int argc, char *argv[]) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}