#include "hardware_unit_tests.hh"

UTEST_STATE();

CPP_AT_CALLBACK(ATTestCallback) {
    int argc = 0;
    const char* argv[1];
    return utest_main(argc, argv) == 0;
}