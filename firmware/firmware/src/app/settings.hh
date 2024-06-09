#ifndef SETTINGS_HH_
#define SETTINGS_HH_

#include "ads_bee.hh"
#include "eeprom.hh"

class SettingsManager {
   public:
    struct Settings {
        // ADSBee settings
        int tl_lo_mv = ADSBee::kTLLoDefaultMV;
        int tl_hi_mv = ADSBee::kTLHiDefaultMV;
        uint16_t rx_gain = ADSBee::kRxGainDefault;

        // CommunicationsManager settings
    };

    /**
     * Loads settings from EEPROM. Assumes settings are stored at address 0x0 and doesn't do any integrity check.
     * @retval True if succeeded, false otherwise.
     */
    bool Load() {
        if (!eeprom.Load(settings)) {
            return false;
        };

        Apply();

        return true;
    }

    /**
     * Saves settings to EEPROM. Stores settings at address 0x0 and performs no integrity check.
     * @retval True if succeeded, false otherwise.
     */
    bool Save() {
        settings.rx_gain = ads_bee.GetRxGain();
        settings.tl_lo_mv = ads_bee.GetTLLoMilliVolts();
        settings.tl_hi_mv = ads_bee.GetTLHiMilliVolts();
        return eeprom.Save(settings);
    }

    /**
     * Restores settings to factory default values.
     */
    void ResetToDefaults() {
        Settings default_settings;
        settings = default_settings;
        Apply();
    }

    Settings settings;

   private:
    /**
     * Applies internal settings to the relevant objects.
     */
    void Apply() {
        ads_bee.SetTLLoMilliVolts(settings.tl_lo_mv);
        ads_bee.SetTLHiMilliVolts(settings.tl_hi_mv);
        ads_bee.SetRxGain(settings.rx_gain);
    }
};

extern SettingsManager settings_manager;

#endif /* SETTINGS_HH_ */