# NASA Compact Position Reporting (CPR) Library

This folder contains files adapted from the [formally verified CPR decoding library](https://github.com/nasa/cpr) provided by NASA under an open source license. For license details, see the License PDF in this directory.

ADSBee uses the fixed-point implementation of the CPR decode library in order to optimize performance on devices that do not have an FPU. CPR code has been migrated to C++ by the ADSBee project in order to allow use of namespaces to avoid conflicts between functions that are duplicated across the CPR libraries used for surface and airborne position decoding.

## Folders
* `airborne` - This CPR implementation is used for decoding airborne position messages.
* `surface` - This CPR implementation is used for decoding position messages from emitters on the ground.

NOTE: There are also implementations available for `coarse` position representations as well as `intent` position representations, but these are not currently included nor used by ADSBee.