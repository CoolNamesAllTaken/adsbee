#ifndef UNIT_CONVERSIONS_HH_
#define UNIT_CONVERSIONS_HH_

inline int FeetToMeters(int feet) { return feet * 1000 / 3280; }

inline int MetersToFeet(int meters) { return meters * 3280 / 1000; }

#endif