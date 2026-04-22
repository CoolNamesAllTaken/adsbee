#include "comms.hh"  // For debug logging.
#include "utest.h"

// #define TEST_EEPROM

CPP_AT_CALLBACK(ATTestCallback);
CPP_AT_CALLBACK(ATIngestModeSCallback);  // AT+INGEST_MODE_S
CPP_AT_CALLBACK(ATIngestUATCallback);    // AT+INGEST_UAT