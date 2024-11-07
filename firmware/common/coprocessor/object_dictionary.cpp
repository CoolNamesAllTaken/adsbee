#include "object_dictionary.hh"

const uint8_t ObjectDictionary::kFirmwareVersionMajor = 0;
const uint8_t ObjectDictionary::kFirmwareVersionMinor = 5;
const uint8_t ObjectDictionary::kFirmwareVersionPatch = 2;

const uint32_t ObjectDictionary::kFirmwareVersion =
    (kFirmwareVersionMajor) << 16 | (kFirmwareVersionMinor) << 8 | (kFirmwareVersionPatch);