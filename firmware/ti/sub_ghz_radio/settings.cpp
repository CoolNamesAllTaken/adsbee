#include "settings.hh"

#include "sub_ghz_radio.hh"
#include "sub_ghz_radio_configs.hh"

bool SettingsManager::Apply() {
    subg_radio.SetConfig(kSubGRadioConfigs[static_cast<uint8_t>(settings.subg_mode)]);
    CONSOLE_PRINTF("SettingsManager::Apply: Applied Sub-GHz radio configuration for mode %s.\r\n",
                   kSubGModeStrs[settings.subg_mode]);
    // Note: SubGHz radio may need to be de-init'ed and re-init'ed if the configuration has changed.
    subg_radio.rx_enabled = settings.subg_rx_enabled;
    subg_radio.SetBiasTeeEnable(settings.subg_bias_tee_enabled);
    return true;
}