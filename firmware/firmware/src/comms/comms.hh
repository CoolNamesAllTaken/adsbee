#ifndef COMMS_HH_
#define COMMS_HH_

#include "cpp_at.hh"

class CommsManager {
   public:
    static const uint16_t kATCommandBufMaxLen = 1000;

    enum ATConfigMode : uint16_t { kRun = 0, kConfig = 1, kInvalid = 2 };

    struct CommsManagerConfig {};

    CommsManager(CommsManagerConfig config_in);
    bool Init();
    bool Update();

    CPP_AT_CALLBACK(ATConfigCallback);
    CPP_AT_CALLBACK(ATMTLSetCallback);
    CPP_AT_CALLBACK(ATMTLReadCallback);
    CPP_AT_CALLBACK(ATRxGainCallback);

    int debug_printf(const char *format, ...);

   private:
    CommsManagerConfig config_;
    CppAT at_parser_;

    ATConfigMode at_config_mode_ = ATConfigMode::kRun;

    bool InitAT();
    bool UpdateAT();
};

extern CommsManager comms_manager;

#define DEBUG_PRINTF(format, ...) comms_manager.debug_printf(format __VA_OPT__(, ) __VA_ARGS__);

#endif /* COMMS_HH_ */