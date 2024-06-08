#ifndef UNIT_CONVERSIONS_HH_
#define UNIT_CONVERSIONS_HH_

inline int FeetToMeters(int feet) { return feet * 1000 / 3280; }

inline int MetersToFeet(int meters) { return meters * 3280 / 1000; }

inline int KtsToMps(int kts) { kts * 5144 / 10000; }

inline int MpsToKts(int mps) { mps * 10000 / 5144; }

inline int FpmToMps(int fpm) { fpm * 508 / 100000; }

#endif