#ifndef _COMMS_HH_
#define _COMMS_HH_

#include "ads_bee.hh"
#include "cpp_at.hh"

class CommsManager {
   public:
    static const uint16_t kATCommandBufMaxLen = 1000;

    enum ATConfigMode : uint16_t { kRun = 0, kConfig = 1, kInvalid = 2 };

    struct CommsManagerConfig {
        ADSBee &ads_bee;
    };

    CommsManager(CommsManagerConfig config_in);
    bool Init();
    bool Update();

    CPP_AT_CALLBACK(ATConfigCallback);
    CPP_AT_CALLBACK(ATMTLSetCallback);
    CPP_AT_CALLBACK(ATMTLReadCallback);
    CPP_AT_CALLBACK(ATRxGainCallback);

   private:
    CommsManagerConfig config_;
    CppAT at_parser_;
    ADSBee &ads_bee_;

    ATConfigMode at_config_mode_ = ATConfigMode::kRun;

    bool InitAT();
    bool UpdateAT();
};

extern CommsManager comms_manager;

#endif /* _COMMS_HH_ */