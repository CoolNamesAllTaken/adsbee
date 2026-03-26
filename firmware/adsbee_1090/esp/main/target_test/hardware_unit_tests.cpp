#include "hardware_unit_tests.hh"

UTEST_STATE();

// For some reason the ESP IDF isn't collecting the UTEST cases in other .cpp files, so we need to explicitly include
// them here for each file.
#include "test_spi_coprocessor.cpp"

static bool utest_main_called = false;
bool RunHardwareUnitTests() {
    if (!utest_main_called) {
        int argc = 0;
        char* argv[1] = {nullptr};
        int ret = utest_main(argc, argv);
        utest_main_called = true;
        if (ret >= 0) {
            return true;
        } else {
            CONSOLE_ERROR("RunHardwareUnitTests", "utest_main returned code %d", ret);
            return false;
        }
    }

    CONSOLE_ERROR("RunHardwareUnitTests", "Can't run utest_main multiple times because it'll break (janky af).");
    return false;
}