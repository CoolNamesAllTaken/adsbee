#include "adsbee.hh"
#include "beast_utils.hh"
#include "comms.hh"
#include "composite_array.hh"
#include "csbee_utils.hh"
#include "gdl90_utils.hh"
#include "hal.hh"  // For timestamping.
#include "mavlink_utils.hh"
#include "raw_utils.hh"
#include "spi_coprocessor.hh"
#include "unit_conversions.hh"

static constexpr uint16_t kMaxNumModeSPacketsToReport = 100;
static constexpr uint16_t kMaxNumUATADSBPacketsToReport = 50;
static constexpr uint16_t kMaxNumUATUplinkPacketsToReport = 2;

extern ADSBee adsbee;
