#pragma once

#include <cstdint>
#include "driver/gpio.h"
#include "driver/i2c_master.h"
#include "esp_err.h"
#include "bsp.hh"

// MP2722 5A Single-Cell I2C-Controlled NVDC Buck Charger Driver
// Datasheet: MP2722 Rev. 1.0, Monolithic Power Systems, 11/3/2022

class Mp2722 {
 public:
  // I2C address — fixed, per datasheet p.28 ("I2C Slave Address: 3Fh")
  static constexpr uint8_t kI2cAddress = 0x3F;

  // -------------------------------------------------------------------------
  // Configuration register addresses (R/W, REG00h–REG10h)
  // -------------------------------------------------------------------------
  static constexpr uint8_t kRegGlobalCfg      = 0x00;  // SW_FREQ, EN_VIN_TRK, etc.
  static constexpr uint8_t kRegInputCurrentCfg = 0x01;  // IIN_MODE, IIN_LIM
  static constexpr uint8_t kRegChgCurrentCfg  = 0x02;  // VPRE, ICC
  static constexpr uint8_t kRegPreChgTermCfg  = 0x03;  // IPRE, ITERM
  static constexpr uint8_t kRegRechargeVolt   = 0x04;  // VRECHG, ITRICKLE, VIN_LIM
  static constexpr uint8_t kRegChgVoltTimer   = 0x05;  // TOPOFF_TMR, VBATT
  static constexpr uint8_t kRegOvpSysMinTreg  = 0x06;  // VIN_OVP, SYS_MIN, TREG
  static constexpr uint8_t kRegWatchdogTimer  = 0x07;  // IB_EN, WATCHDOG_RST, WATCHDOG, CHG_TIMER
  static constexpr uint8_t kRegBatfetBoost    = 0x08;  // BATTFET_DIS, OLIM, VBOOST
  static constexpr uint8_t kRegCcBuckChg     = 0x09;  // CC_CFG, AUTOOTG, EN_BOOST, EN_BUCK, EN_CHG
  static constexpr uint8_t kRegDpdmCfg       = 0x0A;  // AUTODPDM, FORCEDPDM, RP_CFG, FORCE_CC
  static constexpr uint8_t kRegHvAdapter     = 0x0B;  // HVEN, HVUP, HVDOWN, HVREQ
  static constexpr uint8_t kRegNtcBoostCfg   = 0x0C;  // NTC1_ACTION, NTC2_ACTION, BATT_OVP_EN, etc.
  static constexpr uint8_t kRegJeitaCfg      = 0x0D;  // WARM_ACT, COOL_ACT, JEITA_VSET, JEITA_ISET
  static constexpr uint8_t kRegNtcThresh     = 0x0E;  // VHOT, VWARM, VCOOL, VCOLD
  static constexpr uint8_t kRegVinTest       = 0x0F;  // VIN_SRC_EN, IVIN_SRC, VIN_TEST
  static constexpr uint8_t kRegIntMask       = 0x10;  // MASK_* interrupt mask bits

  // -------------------------------------------------------------------------
  // Status register addresses (R/O, REG11h–REG16h)
  // -------------------------------------------------------------------------
  static constexpr uint8_t kRegDpdmStat      = 0x11;  // DPDM_STAT, VINDPM_STAT, IINDPM_STAT
  static constexpr uint8_t kRegVinStat       = 0x12;  // VIN_GD, VIN_RDY, THERM_STAT, WATCHDOG_FAULT
  static constexpr uint8_t kRegChgFaultStat  = 0x13;  // CHG_STAT, BOOST_FAULT, CHG_FAULT
  static constexpr uint8_t kRegNtcFaultStat  = 0x14;  // NTC_MISSING, BATT_MISSING, NTC1_FAULT, NTC2_FAULT
  static constexpr uint8_t kRegCcStat        = 0x15;  // CC1/CC2 SNK/SRC status
  static constexpr uint8_t kRegMiscStat      = 0x16;  // TOPOFF_ACTIVE, BFET_STAT, OTG_NEED, etc.

  // -------------------------------------------------------------------------
  // REG11h (DPDM status) bit fields
  // -------------------------------------------------------------------------
  static constexpr uint8_t kDpdmStatMask     = 0xF0;
  static constexpr uint8_t kDpdmStatShift    = 4;
  static constexpr uint8_t kVindpmStatMask   = (1 << 1);
  static constexpr uint8_t kIindpmStatMask   = (1 << 0);

  // -------------------------------------------------------------------------
  // REG12h (VIN / watchdog status) bit fields
  // -------------------------------------------------------------------------
  static constexpr uint8_t kVinGdMask        = (1 << 6);  // 1 = valid input source present
  static constexpr uint8_t kVinRdyMask       = (1 << 5);  // 1 = input type detection complete
  static constexpr uint8_t kLegacyCableMask  = (1 << 4);
  static constexpr uint8_t kThermStatMask    = (1 << 3);  // 1 = in thermal regulation
  static constexpr uint8_t kVsysStatMask     = (1 << 2);
  static constexpr uint8_t kWatchdogFaultMask = (1 << 1);  // 1 = watchdog expired
  static constexpr uint8_t kWatchdogBarkMask  = (1 << 0);  // 1 = 3/4 watchdog expired

  // -------------------------------------------------------------------------
  // REG13h (charge / fault status) bit fields
  // -------------------------------------------------------------------------
  static constexpr uint8_t kChgStatMask          = 0xE0;
  static constexpr uint8_t kChgStatShift         = 5;
  static constexpr uint8_t kChgStatNotCharging   = 0x00;
  static constexpr uint8_t kChgStatTrickle       = 0x01;
  static constexpr uint8_t kChgStatPreCharge     = 0x02;
  static constexpr uint8_t kChgStatFastCharge    = 0x03;
  static constexpr uint8_t kChgStatCvCharge      = 0x04;  // constant-voltage phase
  static constexpr uint8_t kChgStatDone          = 0x05;
  static constexpr uint8_t kBoostFaultMask       = 0x1C;
  static constexpr uint8_t kBoostFaultShift      = 2;
  static constexpr uint8_t kChgFaultMask         = 0x03;
  static constexpr uint8_t kChgFaultShift        = 0;
  static constexpr uint8_t kChgFaultNormal       = 0x00;
  static constexpr uint8_t kChgFaultInputOvp     = 0x01;
  static constexpr uint8_t kChgFaultTimerExpired = 0x02;
  static constexpr uint8_t kChgFaultBattOvp      = 0x03;

  // -------------------------------------------------------------------------
  // REG07h (watchdog / timer config) bit fields
  // -------------------------------------------------------------------------
  static constexpr uint8_t kWatchdogRstBit   = (1 << 6);  // write 1 to reset (self-clearing)
  static constexpr uint8_t kWatchdogMask     = 0x30;
  static constexpr uint8_t kWatchdogDisable  = 0x00;
  static constexpr uint8_t kWatchdog40s      = 0x10;
  static constexpr uint8_t kWatchdog80s      = 0x20;
  static constexpr uint8_t kWatchdog160s     = 0x30;

  // -------------------------------------------------------------------------
  // Timing constants (ms)
  // -------------------------------------------------------------------------
  static constexpr uint32_t kStartupTimeMs  = 5;

  // -------------------------------------------------------------------------
  // Configuration — passed to the constructor.
  // -------------------------------------------------------------------------
  struct Config {
    // I2C bus configuration. Init() calls i2c_master_get_bus_handle() first;
    // if the port already has a bus (created by another driver) the existing
    // handle is reused and no new bus is created. If the port is unclaimed,
    // the driver creates and owns the bus and tears it down in Deinit().
    i2c_port_num_t i2c_port  = bsp.periph_i2c_port;
    gpio_num_t     sda_pin   = bsp.periph_i2c_sda_pin;
    gpio_num_t     scl_pin   = bsp.periph_i2c_scl_pin;

    // I2C clock speed for this device (Hz). Max 400 kHz per datasheet.
    uint32_t i2c_speed_hz = 400000;

    // If true, the watchdog timer is disabled during Init() so custom register
    // settings are preserved indefinitely. Set to false and call
    // KickWatchdog() periodically if you want the watchdog active.
    bool disable_watchdog = true;
  };

  Mp2722() : Mp2722(Config{}) {}
  explicit Mp2722(const Config& config);
  ~Mp2722();

  Mp2722(const Mp2722&)            = delete;
  Mp2722& operator=(const Mp2722&) = delete;

  // -------------------------------------------------------------------------
  // Lifecycle
  // -------------------------------------------------------------------------
  bool Init();
  bool Deinit();
  bool IsInitialized() const { return i2c_handle_ != nullptr; }

  // -------------------------------------------------------------------------
  // Control (call only after Init())
  // -------------------------------------------------------------------------

  // Reads REG12h–REG13h and updates all cached status fields.
  bool Update();

  // Resets the hardware watchdog by writing WATCHDOG_RST in REG07h.
  bool KickWatchdog();

  // -------------------------------------------------------------------------
  // Getters
  // -------------------------------------------------------------------------

  // True when VIN_GD = 1: a valid input source is present on VIN.
  bool IsPowerGood()            const { return power_good_; }

  // True while the charger is actively delivering current to the battery
  // (trickle, pre-charge, fast charge, or CV charge). "Done" is excluded.
  bool IsCharging()             const { return is_charging_; }

  enum class ChargeStatus : uint8_t {
    kNotCharging = kChgStatNotCharging,
    kTrickle     = kChgStatTrickle,
    kPreCharge   = kChgStatPreCharge,
    kFastCharge  = kChgStatFastCharge,
    kCvCharge    = kChgStatCvCharge,
    kDone        = kChgStatDone,
  };
  ChargeStatus GetChargeStatus()       const { return charge_status_; }

  bool IsInThermalRegulation()         const { return thermal_regulation_; }
  bool HasWatchdogFault()              const { return watchdog_fault_; }
  bool HasChgFault()                   const { return chg_fault_ != 0; }
  bool HasBoostFault()                 const { return boost_fault_ != 0; }

  uint8_t GetRawVinStat()              const { return raw_vin_stat_; }
  uint8_t GetRawChgFaultStat()         const { return raw_chg_fault_stat_; }

 private:
  esp_err_t WriteReg(uint8_t reg, uint8_t value);
  esp_err_t ReadReg(uint8_t reg, uint8_t* value);
  esp_err_t ModifyReg(uint8_t reg, uint8_t mask, uint8_t value);
  void      ParseStatus(uint8_t vin_stat, uint8_t chg_fault_stat);

  const Config            config_;
  i2c_master_dev_handle_t i2c_handle_       = nullptr;
  i2c_master_bus_handle_t owned_bus_handle_ = nullptr;

  bool         power_good_         = false;
  bool         is_charging_        = false;
  bool         thermal_regulation_ = false;
  bool         watchdog_fault_     = false;
  uint8_t      chg_fault_          = 0;
  uint8_t      boost_fault_        = 0;
  ChargeStatus charge_status_      = ChargeStatus::kNotCharging;

  uint8_t raw_vin_stat_       = 0;
  uint8_t raw_chg_fault_stat_ = 0;
};
