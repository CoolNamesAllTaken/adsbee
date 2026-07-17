#pragma once

#include <cstdint>
#include "driver/gpio.h"
#include "driver/i2c_master.h"
#include "esp_err.h"
#include "esp_timer.h"
#include "bsp.hh"

// BQ27427 System-Side Impedance Track Fuel Gauge Driver
// Technical Reference Manual: SLUUCD5, Texas Instruments, January 2023
// https://www.ti.com/lit/pdf/sluucd5

class Bq27427 {
 public:
  // 7-bit I2C address is fixed at 0x55 (binary 1010101).
  // 8-bit write / read bytes are 0xAA / 0xAB per the TRM.
  static constexpr uint8_t kI2cAddress = 0x55;

  // -------------------------------------------------------------------------
  // Standard Command addresses (TRM Section 5)
  // All standard commands are 2 bytes, read LSB-first (little-endian).
  // -------------------------------------------------------------------------
  static constexpr uint8_t kCmdControl          = 0x00;  // Control() — write subcommand word here
  static constexpr uint8_t kCmdTemperature      = 0x02;  // Temperature() — units: 0.1 K
  static constexpr uint8_t kCmdVoltage          = 0x04;  // Voltage() — units: mV, unsigned
  static constexpr uint8_t kCmdFlags            = 0x06;  // Flags() — status bits, see below
  static constexpr uint8_t kCmdNomCapacity      = 0x08;  // NominalAvailableCapacity() — mAh
  static constexpr uint8_t kCmdFullAvailCap     = 0x0A;  // FullAvailableCapacity() — mAh
  static constexpr uint8_t kCmdRemCapacity      = 0x0C;  // RemainingCapacity() — mAh
  static constexpr uint8_t kCmdFullChargeCap    = 0x0E;  // FullChargeCapacity() — mAh
  static constexpr uint8_t kCmdAverageCurrent   = 0x10;  // AverageCurrent() — mA, signed
  static constexpr uint8_t kCmdAveragePower     = 0x18;  // AveragePower() — mW, signed
  static constexpr uint8_t kCmdStateOfCharge    = 0x1C;  // StateOfCharge() — %, unsigned
  static constexpr uint8_t kCmdInternalTemp     = 0x1E;  // InternalTemperature() — 0.1 K

  // -------------------------------------------------------------------------
  // Control() subcommands (write to kCmdControl as a little-endian uint16)
  // -------------------------------------------------------------------------
  static constexpr uint16_t kSubCmdControlStatus = 0x0000;  // Read CONTROL_STATUS word
  static constexpr uint16_t kSubCmdDeviceType    = 0x0001;  // Read device type (should be 0x0427)
  static constexpr uint16_t kSubCmdChemId        = 0x0008;  // Read the active chemistry ID
  static constexpr uint16_t kSubCmdBatInsert     = 0x000C;  // Signal battery insertion
  static constexpr uint16_t kSubCmdSetCfgUpdate  = 0x0013;  // Enter CONFIG UPDATE mode
  static constexpr uint16_t kSubCmdSealed        = 0x0020;  // Re-seal the device
  static constexpr uint16_t kSubCmdChemA         = 0x0030;  // Select Chem A (3230, 4.35 V)
  static constexpr uint16_t kSubCmdChemB         = 0x0031;  // Select Chem B (1202, 4.2 V)
  static constexpr uint16_t kSubCmdChemC         = 0x0032;  // Select Chem C (3142, 4.4 V)
  static constexpr uint16_t kSubCmdSoftReset     = 0x0042;  // Soft reset (exits CONFIG UPDATE)
  static constexpr uint16_t kSubCmdUnseal        = 0x8000;  // UNSEAL key (sent twice)

  // Chemistry IDs returned by kSubCmdChemId, one per profile.
  static constexpr uint16_t kChemIdA = 3230;  // 4.35 V
  static constexpr uint16_t kChemIdB = 1202;  // 4.2 V
  static constexpr uint16_t kChemIdC = 3142;  // 4.4 V

  // Extended Data commands (block data memory access, TRM Section 6).
  static constexpr uint8_t kCmdDataClass         = 0x3E;  // DataClass() — subclass id
  static constexpr uint8_t kCmdDataBlock         = 0x3F;  // DataBlock() — 32-byte block offset
  static constexpr uint8_t kCmdBlockData         = 0x40;  // BlockData() — start of the 32-byte block
  static constexpr uint8_t kCmdBlockDataChecksum = 0x60;  // BlockDataChecksum()
  static constexpr uint8_t kCmdBlockDataControl  = 0x61;  // BlockDataControl() (0x00 = enable)

  // Data-memory location of the parameters we program (State subclass 0x52,
  // TRM Data Flash Summary). Offsets are within the 32-byte block; the byte
  // address in the BlockData window is kCmdBlockData + (offset % 32).
  static constexpr uint8_t kDmStateSubclass       = 0x52;  // State subclass (82)
  static constexpr uint8_t kDmDesignCapacityOffset  = 6;   // I2, mAh (0x46/0x47)
  static constexpr uint8_t kDmTerminateVoltageOffset = 10; // I2, mV  (0x4A/0x4B)

  // -------------------------------------------------------------------------
  // Flags() register bit masks (kCmdFlags, TRM Section 5.4)
  // -------------------------------------------------------------------------
  static constexpr uint16_t kFlagDischarging   = (1 << 0);   // [DSG]  — 1 = discharging
  static constexpr uint16_t kFlagSocf          = (1 << 1);   // [SOCF] — state-of-charge final
  static constexpr uint16_t kFlagSoc1          = (1 << 2);   // [SOC1] — state-of-charge initial
  static constexpr uint16_t kFlagBatDetect     = (1 << 3);   // [BAT_DET] — battery detected
  static constexpr uint16_t kFlagWaitId        = (1 << 4);   // [WAIT_ID] — waiting for battery ID
  static constexpr uint16_t kFlagOcvTaken      = (1 << 5);   // [OCVTAKEN] — OCV measurement done
  static constexpr uint16_t kFlagDodCorrect    = (1 << 6);   // [DODCORRECT]
  static constexpr uint16_t kFlagItpor         = (1 << 13);  // [ITPOR] — RAM initialised to ROM defaults (POR)
  static constexpr uint16_t kFlagCfgUpMode     = (1 << 4);   // [CFGUPMODE] — in CONFIG UPDATE mode
  static constexpr uint16_t kFlagFullCharge    = (1 << 9);   // [FC] — full charge detected
  static constexpr uint16_t kFlagCharging      = (1 << 8);   // [CHG] — fast charging allowed

  // -------------------------------------------------------------------------
  // Timing constants (ms)
  // -------------------------------------------------------------------------
  // After power-on, wait for INITIALIZATION to complete before polling data.
  static constexpr uint32_t kInitWaitMs         = 250;
  // The TRM requires read-only standard commands to not exceed 2 calls/second.
  // Update() internally enforces this; safe to call every loop tick.
  static constexpr uint32_t kMinUpdateIntervalMs = 500;

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

    // I2C clock speed. The BQ27427 supports 100 kHz and 400 kHz modes.
    uint32_t i2c_speed_hz = 400000;

    // If true (default), Init() sends a BAT_INSERT subcommand to signal
    // battery presence to the gauge. Set to false if your hardware uses
    // the BIN pin for battery detection (OpConfig [BIE] = 1).
    bool send_bat_insert = true;

    // Battery spec configuration (Init() programs these via CONFIG UPDATE so the
    // SOC estimate is accurate). If configure_battery is false, the gauge keeps
    // its current/default configuration. chem_profile: 0=A(4.35V), 1=B(4.2V),
    // 2=C(4.4V). Defaults come from bsp.hh.
    bool     configure_battery    = true;
    uint16_t design_capacity_mah  = bsp.battery_design_capacity_mah;
    uint16_t terminate_voltage_mv = bsp.battery_terminate_voltage_mv;
    uint8_t  chem_profile         = bsp.battery_chem_profile;
  };

  Bq27427() : Bq27427(Config{}) {}
  explicit Bq27427(const Config& config);
  ~Bq27427();

  Bq27427(const Bq27427&)            = delete;
  Bq27427& operator=(const Bq27427&) = delete;

  // -------------------------------------------------------------------------
  // Lifecycle
  // -------------------------------------------------------------------------

  // Registers the device on the bus, verifies the device type, optionally
  // signals battery insertion, and reads the initial set of measurements.
  bool Init();

  // Removes the device from the bus and releases handles owned by this driver.
  bool Deinit();

  bool IsInitialized() const { return i2c_handle_ != nullptr; }

  // -------------------------------------------------------------------------
  // Sensor polling (call only after Init())
  // -------------------------------------------------------------------------

  // Reads AveragePower() and StateOfCharge() from the gauge and caches the
  // results. Internally enforces kMinUpdateIntervalMs between I2C transactions;
  // safe to call every loop tick — throttled calls return true immediately.
  bool Update();

  // -------------------------------------------------------------------------
  // Getters — return values from the most recent successful Update() call.
  // -------------------------------------------------------------------------

  // Average power in milliwatts (signed). Negative = discharging.
  int16_t  GetAveragePowerMw()   const { return average_power_mw_; }

  // State of charge in percent, 0–100.
  uint16_t GetStateOfChargePct() const { return state_of_charge_pct_; }

  // Remaining capacity in mAh.
  uint16_t GetRemainingCapacityMah() const { return remaining_capacity_mah_; }

  // Average current in mA (signed). Negative = discharging.
  int16_t  GetAverageCurrentMa()     const { return average_current_ma_; }

  // Estimated time-to-empty in minutes, computed from RemainingCapacity /
  // |AverageCurrent| (the gauge has no direct TimeToEmpty command). Returns -1
  // when charging, when the current is ~zero, or when data is invalid.
  int32_t GetTimeToEmptyMinutes() const {
    if (!data_valid_ || average_current_ma_ >= 0) return -1;  // charging / idle / invalid
    int32_t discharge_ma = -(int32_t)average_current_ma_;
    if (discharge_ma <= 0) return -1;
    return (int32_t)((int64_t)remaining_capacity_mah_ * 60 / discharge_ma);
  }

  // Raw Flags() word — available for diagnostics without an extra I2C read.
  uint16_t GetFlags()            const { return flags_; }

  // True when [BAT_DET] is set and [ITPOR] / [CFGUPMODE] are clear —
  // i.e. the gauge is in NORMAL mode and its readings are valid.
  bool IsDataValid()             const { return data_valid_; }

 private:
  esp_err_t WriteSubCmd(uint16_t subcmd);
  esp_err_t ReadWord(uint8_t cmd, uint16_t* out);
  esp_err_t ReadWordSigned(uint8_t cmd, int16_t* out);
  esp_err_t WriteByte(uint8_t cmd, uint8_t value);
  esp_err_t ReadByte(uint8_t cmd, uint8_t* out);

  // Poll Flags() until (flags & mask) matches `set` (true = wait for set bit,
  // false = wait for clear), or the timeout elapses. Returns ESP_OK on match.
  esp_err_t WaitFlag(uint16_t mask, bool set, uint32_t timeout_ms);

  // Program the cell's Design Capacity / Terminate Voltage / chemistry via the
  // CONFIG UPDATE flow (TRM Section 4). Each parameter is written only if it
  // differs from the current value. Returns true on success (or nothing to do).
  bool ConfigureBattery();
  esp_err_t Unseal();
  esp_err_t SelectChemProfile(uint8_t profile);  // returns ESP_OK, sets *changed
  // Read/write a 2-byte big-endian parameter in the State subclass block. The
  // caller must already be in CONFIG UPDATE mode.
  esp_err_t ReadStateParam(uint8_t offset, int16_t* out);
  esp_err_t WriteStateParam(uint8_t offset, int16_t value);

  const Config            config_;
  i2c_master_dev_handle_t i2c_handle_       = nullptr;
  i2c_master_bus_handle_t owned_bus_handle_ = nullptr;

  // Timestamp (µs) of the last completed I2C transaction.
  // Initialised to 0 so the first call always proceeds.
  int64_t  last_update_us_      = 0;

  int16_t  average_power_mw_      = 0;
  uint16_t state_of_charge_pct_   = 0;
  uint16_t remaining_capacity_mah_ = 0;
  int16_t  average_current_ma_    = 0;
  uint16_t flags_                 = 0;
  bool     data_valid_            = false;
};
