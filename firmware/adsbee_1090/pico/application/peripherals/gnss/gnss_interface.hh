#pragma once

#include <new>  // For placement new.

#include "bsp.hh"            // For BSP::GNSSModuleType.
#include "gnss_receiver.hh"  // Base type used by the `gnss` reference.

// ============================================================================
//  ADD A NEW GNSS MODULE HERE — everything for a new vendor lives in this block:
//    1. #include its receiver header.
//    2. Add it as a member of GNSSReceiverStorage.
//    3. Add a `case` to MakeGNSSReceiver() mapping its BSP::GNSSModuleType -> class.
//  (Plus, in bsp.hh: add the enum value and its part-number case in the BSP switch.)
// ============================================================================

// 1. Concrete receiver headers.
#include "none_gnss_receiver.hh"
#include "ublox_max_m10.hh"

// 2. Backing storage for the selected receiver. Exactly one member is ever constructed; the union is
//    sized/aligned to the largest receiver. `inline` gives it a single definition shared across every
//    translation unit that includes this header (C++17+).
union GNSSReceiverStorage {
    NoneGNSSReceiver none;
    UbloxMAXM10 ublox;
    GNSSReceiverStorage() {}   // Members are constructed via placement new in MakeGNSSReceiver().
    ~GNSSReceiverStorage() {}  // Forever-lived global; never destroyed.
};
inline GNSSReceiverStorage gnss_storage;

// 3. Map the board's GNSS module type to a concrete receiver: placement-new the selected type into
//    gnss_storage and return it. No heap; the returned reference lives for the program's lifetime.
inline GNSSReceiver& MakeGNSSReceiver(BSP::GNSSModuleType type) {
    switch (type) {
        case BSP::kGNSSModuleUbloxMAXM10:
            return *new (&gnss_storage.ublox) UbloxMAXM10({});
        case BSP::kGNSSModuleNone:
        default:
            return *new (&gnss_storage.none) NoneGNSSReceiver({});
    }
}
// ============================ end add-a-module block =========================

// The application-wide GNSS receiver (defined in main.cc, next to the other board globals).
extern GNSSReceiver& gnss;
