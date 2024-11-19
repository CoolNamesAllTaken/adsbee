#ifndef UNIT_CONVERSIONS_HH_
#define UNIT_CONVERSIONS_HH_

static const int kUsPerMs = 1000;
static const int kMsPerSec = 1000;
static const int kBytesPerWord = 4;
static const int kBitsPerByte = 8;
static const int kBitsPerNibble = 4;

inline uint16_t CeilBitsToBytes(uint16_t bits) { return (bits + kBitsPerByte - 1) / kBitsPerByte; }

inline int FeetToMeters(int feet) { return feet * 1000 / 3280; }

inline int MetersToFeet(int meters) { return meters * 3280 / 1000; }

inline int KtsToMps(int kts) { return kts * 5144 / 10000; }

inline int MpsToKts(int mps) { return mps * 10000 / 5144; }

inline int FpmToMps(int fpm) { return fpm * 508 / 100000; }

#endif