#include "hardware_unit_tests.hh"

#include "eeprom.hh"

UTEST_STATE();

static bool utest_main_called = false;

CPP_AT_CALLBACK(ATTestCallback) {
    if (op == '=') {
        if (CPP_AT_HAS_ARG(0)) {
            if (args[0].compare("DUMP_EEPROM") == 0) {
                eeprom.Dump();
                CPP_AT_SILENT_SUCCESS();
            } else if (args[0].compare("CLEAR_EEPROM") == 0) {
                uint16_t eeprom_size_bytes = eeprom.GetSizeBytes();
                uint8_t buf[eeprom_size_bytes];
                memset(buf, 0xFF, eeprom_size_bytes);
                eeprom.WriteBuf(0x0, buf, eeprom_size_bytes);
                CPP_AT_SUCCESS();
            }
        }
    }

    if (!utest_main_called) {
        int argc = 0;
        const char* argv[1];
        int ret = utest_main(argc, argv);
        utest_main_called = true;
        if (ret >= 0) {
            CPP_AT_SUCCESS();
        } else {
            CPP_AT_ERROR("utest_main returned code %d", ret);
        }
    }

    CPP_AT_ERROR("Can't run utest_main multiple times because it'll break (janky af).");
}