#ifndef ADSBEE_SERVER_HH_
#define ADSBEE_SERVER_HH_

#include "data_structures.hh"
#include "settings.hh"

class ADSBeeServer
{
public:
    ADSBeeServer()
    {
        for (uint16_t i = 0; i < SettingsManager::kMaxNumFeeds; i++)
        {
        }
    }
};
#endif /* ADSBEE_SERVER_HH_ */