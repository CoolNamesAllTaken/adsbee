#pragma once

#include "gnss_receiver.hh"

/**
 * Placeholder GNSS receiver for boards with no GNSS module populated.
 *
 * IsModulePresent() returns false, so GNSSReceiver::Init() short-circuits without touching any GNSS
 * hardware (no UART claim, no enable-pin toggle, no baud change) and reports the module as absent. The
 * application falls back to its non-GNSS position source, and Update() is the inherited no-op (nothing
 * streams in), so it is always safe to call unconditionally from the main loop.
 */
class NoneGNSSReceiver : public GNSSReceiver {
   public:
    NoneGNSSReceiver(GNSSReceiverConfig config_in) : GNSSReceiver(config_in) {}

   protected:
    bool IsModulePresent() const override { return false; }
    // Never called (Init() short-circuits before using these), but required to make the class concrete.
    uint32_t GetDefaultBaudrate() const override { return 9600; }
    uint32_t GetBootDelayMs() const override { return 0; }
    bool SendInitCommands() override { return false; }
};
