#pragma once

#include <cstdint>
#include <driver/spi_master.h>
#include <driver/gpio.h>
#include "esp_err.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "bsp.hh"
#include "glm/glm.hpp"             // glm::vec3, glm::normalize (geometric)
#include "glm/gtc/quaternion.hpp"  // glm::quat, glm::normalize (quat)

// LSM6DSV 6-Axis IMU Driver (SPI, DMA-capable)
// Implements the embedded advanced features register readout workaround for
// full-precision quaternion data (all 4 components, FP16, page 3 0x4C–0x53).
//
// Workaround rationale: the SFLP FIFO path stores only the 3 vector components
// (X, Y, Z) as FP16, requiring W to be reconstructed via the unit-quaternion
// constraint.  Near 180° rotations, FP16 precision is insufficient to represent
// the required component values, producing visible gaps in the output.  Reading
// the quaternion directly from embedded advanced features page 3 after the
// INT2_EMB_FUNC_ENDOP interrupt gives all 4 components at full FP16 precision
// before the next ODR sample overwrites them.  This page-3 readout is not in
// the datasheet/AN5922; it is an ST FAE workaround from the ST community forum
// ("LSM6DSV half-precision error at 180 degrees").  Byte order at 0x4C is W,X,Y,Z.
//
// Datasheet: https://www.st.com/resource/en/datasheet/lsm6dsv.pdf
// AN5922:    https://www.st.com/resource/en/application_note/an5922-lsm6dsv.pdf
// AN5907:    https://www.st.com/resource/en/application_note/an5907-lsm6dsv.pdf

class Lsm6dsv {
 public:
  // -------------------------------------------------------------------------
  // WHO_AM_I
  // -------------------------------------------------------------------------
  static constexpr uint8_t kWhoAmIValue = 0x70;

  // =========================================================================
  // Register map
  // =========================================================================
  enum Register : uint8_t {
    // -- User interface registers (bank 0, default) --------------------------
    kRegFuncCfgAccess     = 0x01,  // Embedded functions / sensor hub access
    kRegPinCtrl           = 0x02,  // SDO / OCS_Aux / SDO_Aux pin control
    kRegIfCfg             = 0x03,  // Interface config: I2C/I3C disable, SIM, PP_OD, H_LACTIVE
    kRegOdrTrigCfg        = 0x06,  // ODR-triggered mode config
    kRegInt1Ctrl          = 0x0D,  // INT1 control (DRDY etc.)
    kRegInt2Ctrl          = 0x0E,  // INT2 control: INT2_EMB_FUNC_ENDOP (bit7), DRDY
    kRegCtrl1             = 0x10,  // Accelerometer OP_MODE[6:4] / ODR[3:0]  (FS is in CTRL8)
    kRegCtrl2             = 0x11,  // Gyroscope OP_MODE[6:4] / ODR[3:0]      (FS is in CTRL6)
    kRegCtrl3             = 0x12,  // BOOT / BDU / IF_INC / SW_RESET
    kRegCtrl4             = 0x13,  // INT2_on_INT1 / DRDY_MASK / INT2_DRDY_TEMP / DRDY_PULSED
    kRegCtrl5             = 0x14,  // Rounding / self-test
    kRegCtrl6             = 0x15,  // Gyroscope LPF1 BW[6:4] / FS_G[3:0]
    kRegCtrl7             = 0x16,  // LPF1_G_EN
    kRegCtrl8             = 0x17,  // Accel HP_LPF2 BW[7:5] / XL_DualC_EN / FS_XL[1:0]
    kRegCtrl9             = 0x18,  // HP_REF_MODE / XL_FASTSETTL / HP_SLOPE_XL_EN / LPF2_XL_EN
    kRegCtrl10            = 0x19,  // Timestamp enable / OIS
    kRegCtrlEis           = 0x6B,  // EIS ODR/FS/filter
    kRegCtrlOis1          = 0x70,  // OIS accelerometer control
    kRegCtrlOis2          = 0x71,  // OIS gyroscope control (FS)
    kRegCtrlOis3          = 0x72,  // OIS accelerometer FS
    kRegXCoreFall         = 0x73,
    kRegWhoAmI            = 0x0F,  // Device identification (read-only)
    kRegAllIntsrc         = 0x1A,  // Source of all interrupts
    kRegWakeUpSrc         = 0x1B,  // Wake-up interrupt source
    kRegTapSrc            = 0x1C,  // Tap interrupt source
    kRegD6dSrc            = 0x1D,  // 6D/4D interrupt source
    kRegStatusReg         = 0x1E,  // Data ready flags
    kRegStatusSpiAux      = 0x1F,  // Status for OIS channel
    kRegOutTempL          = 0x20,  // Temperature output (°C LSB)
    kRegOutTempH          = 0x21,  // Temperature output (°C MSB)
    kRegOutxLG            = 0x22,  // Gyroscope X output LSB
    kRegOutxHG            = 0x23,
    kRegOutyLG            = 0x24,
    kRegOutyHG            = 0x25,
    kRegOutzLG            = 0x26,
    kRegOutzHG            = 0x27,
    kRegOutxLA            = 0x28,  // Accelerometer X output LSB
    kRegOutxHA            = 0x29,
    kRegOutyLA            = 0x2A,
    kRegOutyHA            = 0x2B,
    kRegOutzLA            = 0x2C,
    kRegOutzHA            = 0x2D,
    kRegUiOutxLOisEisDualC = 0x34, // EIS / dual-channel accel outputs
    kRegUiOutxHOisEisDualC = 0x35,
    kRegUiOutyLOisEisDualC = 0x36,
    kRegUiOutyHOisEisDualC = 0x37,
    kRegUiOutzLOisEisDualC = 0x38,
    kRegUiOutzHOisEisDualC = 0x39,
    kRegTimestamp0        = 0x40,  // Timestamp output (LSB)
    kRegTimestamp1        = 0x41,
    kRegTimestamp2        = 0x42,
    kRegTimestamp3        = 0x43,  // Timestamp output (MSB)
    kRegUiSpoofing        = 0x48,
    kRegQvarStatus        = 0x49,
    kRegWristTiltIa       = 0x55,
    kRegTapCfg0           = 0x56,  // Tap/activity configuration
    kRegTapCfg1           = 0x57,
    kRegTapCfg2           = 0x58,
    kRegTapThs6D          = 0x59,
    kRegIntDur2           = 0x5A,
    kRegWakeUpThs         = 0x5B,
    kRegWakeUpDur         = 0x5C,
    kRegFreeFall          = 0x5D,
    kRegInternalFreqFine  = 0x4F,  // ODR deviation trim (factory value, read-only use)
    kRegMd1Cfg            = 0x5E,  // INT1 routing
    kRegMd2Cfg            = 0x5F,  // INT2 routing
    kRegEmbFuncCfg        = 0x63,  // EMB_FUNC_CFG (user bank): XL/GY settling masks
    kRegUiIntOisReg       = 0x6F,
    kRegFifoCtrl1         = 0x07,  // FIFO watermark LSB
    kRegFifoCtrl2         = 0x08,  // FIFO watermark MSB + stop-on-WTM
    kRegFifoCtrl3         = 0x09,  // Accel / gyro batch ODR
    kRegFifoCtrl4         = 0x0A,  // FIFO mode / timestamp decimation
    kRegCounterBdrReg1    = 0x0B,  // Batch counter threshold
    kRegCounterBdrReg2    = 0x0C,
    kRegFifoStatus1       = 0x1B,  // FIFO fill level LSB
    kRegFifoStatus2       = 0x1C,  // FIFO fill level MSB + overflow flag
    kRegFifoDataOutTag    = 0x78,  // FIFO output tag
    kRegFifoDataOutX_L    = 0x79,  // FIFO output data
    kRegFifoDataOutX_H    = 0x7A,
    kRegFifoDataOutY_L    = 0x7B,
    kRegFifoDataOutY_H    = 0x7C,
    kRegFifoDataOutZ_L    = 0x7D,
    kRegFifoDataOutZ_H    = 0x7E,

    // -- Embedded function bank registers (FUNC_CFG_EN=1) --------------------
    // These share the SPI address space with the user bank but map to a
    // different internal register set.  Access by setting FUNC_CFG_EN=1 first.
    // Addresses that collide with user-bank entries are intentional: the
    // hardware selects the bank via the FUNC_CFG_EN state, not the address.
    kRegEmbFuncEnA        = 0x04,  // EMB_FUNC_EN_A: SFLP_GAME_EN (bit1), tilt, pedo…
    kRegEmbFuncEnB        = 0x05,  // EMB_FUNC_EN_B: FSM / FIFO compression
    kRegEmbFuncExecStatus = 0x07,  // Embedded function execution status
    kRegSflpOdr           = 0x5E,  // SFLP_ODR: SFLP_GAME_ODR[5:3]; bits 6,1,0 fixed=1
    kRegFsmOdr            = 0x5F,  // FSM_ODR
    kRegEmbFuncInt1       = 0x0A,  // EMB_FUNC_INT1 routing
    kRegEmbFuncInitA      = 0x66,  // EMB_FUNC_INIT_A: SFLP_GAME_INIT (bit1)
    kRegEmbFuncInitB      = 0x67,  // EMB_FUNC_INIT_B

    // -- Embedded advanced features page-access registers --------------------
    // Accessed while FUNC_CFG_EN=1.  Select a page via PAGE_SEL, then read/write
    // each register by writing PAGE_ADDRESS and reading/writing PAGE_VALUE.
    kRegPageRw            = 0x17,  // PAGE_RW  : bit5=PAGE_READ, bit6=PAGE_WRITE
    kRegPageSel           = 0x02,  // PAGE_SEL : page number in [7:4], bit0 fixed=1
    kRegPageAddress       = 0x08,  // PAGE_ADDRESS: register address within page
    kRegPageValue         = 0x09,  // PAGE_VALUE  : read/write data
  };

  // =========================================================================
  // CTRL1 (0x10) — Accelerometer
  // =========================================================================

  // Accelerometer output data rate.
  enum class AccelOdr : uint8_t {
    kOdrOff   = 0x00,
    kOdr1Hz875 = 0x01,  // 1.875 Hz  (low-power only)
    kOdr7Hz5  = 0x02,   // 7.5 Hz
    kOdr15Hz  = 0x03,
    kOdr30Hz  = 0x04,
    kOdr60Hz  = 0x05,
    kOdr120Hz = 0x06,
    kOdr240Hz = 0x07,
    kOdr480Hz = 0x08,
    kOdr960Hz = 0x09,
    kOdr1920Hz = 0x0A,
    kOdr3840Hz = 0x0B,
    kOdr7680Hz = 0x0C,
  };

  // Accelerometer full-scale range.
  enum class AccelFs : uint8_t {
    kFs2g  = 0x00,
    kFs4g  = 0x01,
    kFs8g  = 0x02,
    kFs16g = 0x03,
  };

  // Accelerometer operating mode.
  enum class AccelMode : uint8_t {
    kHighPerformance   = 0x00,  // Default; valid for all ODRs
    kHighAccuracyOdr   = 0x01,  // Reduced ODR variation (HAODR)
    kOdrTriggerMode    = 0x03,  // Externally triggered ODR
    kLowPower1         = 0x04,  // Accel low-power mode 1 (2-mean)
    kLowPower2         = 0x05,  // Accel low-power mode 2 (4-mean)
    kLowPower3         = 0x06,  // Accel low-power mode 3 (8-mean)
    kNormalMode        = 0x07,  // Normal mode (OP_MODE_XL = 111)
  };

  // =========================================================================
  // CTRL2 (0x11) — Gyroscope
  // =========================================================================

  // Gyroscope output data rate.
  enum class GyroOdr : uint8_t {
    kOdrOff   = 0x00,
    kOdr7Hz5  = 0x02,
    kOdr15Hz  = 0x03,
    kOdr30Hz  = 0x04,
    kOdr60Hz  = 0x05,
    kOdr120Hz = 0x06,
    kOdr240Hz = 0x07,
    kOdr480Hz = 0x08,
    kOdr960Hz = 0x09,
    kOdr1920Hz = 0x0A,
    kOdr3840Hz = 0x0B,
    kOdr7680Hz = 0x0C,
  };

  // Gyroscope full-scale range.
  enum class GyroFs : uint8_t {
    kFs125dps  = 0x00,
    kFs250dps  = 0x01,
    kFs500dps  = 0x02,
    kFs1000dps = 0x03,
    kFs2000dps = 0x04,
    kFs4000dps = 0x0C,  // 0b1100 per datasheet Table 62 (OIS must be disabled)
  };

  // Gyroscope operating mode.
  enum class GyroMode : uint8_t {
    kHighPerformance = 0x00,
    kHighAccuracyOdr = 0x01,
    kSleep           = 0x02,
    kLowPower        = 0x03,
  };

  // =========================================================================
  // IF_CFG (0x03) — Interface configuration
  // =========================================================================
  static constexpr uint8_t kIfCfgI2cI3cDisable = (1 << 0);  // Disable I2C/I3C (keep set for SPI-only)
  static constexpr uint8_t kIfCfgSim           = (1 << 2);  // SPI mode (0=4-wire, 1=3-wire)
  static constexpr uint8_t kIfCfgPpOd          = (1 << 3);  // INT push-pull / open-drain
  static constexpr uint8_t kIfCfgHLactive      = (1 << 4);  // INT active level (0=high, 1=low)

  // =========================================================================
  // CTRL3 (0x12) — Global control
  // =========================================================================
  static constexpr uint8_t kCtrl3SwReset     = (1 << 0);  // Software reset
  static constexpr uint8_t kCtrl3IfInc       = (1 << 2);  // Auto-increment (must be 1 for SPI burst)
  static constexpr uint8_t kCtrl3Bdu         = (1 << 6);  // Block data update
  static constexpr uint8_t kCtrl3Boot        = (1 << 7);  // Reboot memory content

  // =========================================================================
  // CTRL4 (0x13)
  // =========================================================================
  static constexpr uint8_t kCtrl4Int2InLh      = (1 << 0);  // INT2 input trigger polarity
  static constexpr uint8_t kCtrl4DrdyPulsed    = (1 << 1);  // Pulsed data-ready mode
  static constexpr uint8_t kCtrl4Int2DrdyTemp  = (1 << 2);  // Temperature DRDY on INT2
  static constexpr uint8_t kCtrl4DrdyMask      = (1 << 3);  // Mask DRDY until filter settled
  static constexpr uint8_t kCtrl4Int2OnInt1    = (1 << 4);  // Route INT2 signals to INT1

  // =========================================================================
  // CTRL6 (0x15) — Gyroscope LPF1 bandwidth [6:4] / full-scale [3:0]
  // =========================================================================
  static constexpr uint8_t kCtrl6FsGMask    = 0x0F;  // FS_G_[3:0]
  static constexpr uint8_t kCtrl6Lpf1BwMask = 0x70;  // LPF1_G_BW_[2:0] in bits [6:4]

  enum class GyroLpf1Bw : uint8_t {
    kLpf1Bw0 = 0x00,
    kLpf1Bw1 = 0x01,
    kLpf1Bw2 = 0x02,
    kLpf1Bw3 = 0x03,
    kLpf1Bw4 = 0x04,
    kLpf1Bw5 = 0x05,
    kLpf1Bw6 = 0x06,
    kLpf1Bw7 = 0x07,
  };

  // =========================================================================
  // CTRL8 (0x17) — Accel filter bandwidth [7:5], dual-channel, full-scale [1:0]
  // =========================================================================
  static constexpr uint8_t kCtrl8FsXlMask    = 0x03;  // FS_XL_[1:0]
  static constexpr uint8_t kCtrl8DualCEn     = (1 << 3);  // XL_DualC_EN
  static constexpr uint8_t kCtrl8BwMask      = 0xE0;  // HP_LPF2_XL_BW_[2:0] in bits [7:5]

  // =========================================================================
  // CTRL9 (0x18) — Accel filter enables / fast-settle
  // =========================================================================
  static constexpr uint8_t kCtrl9HpRefMode   = (1 << 6);  // HP_REF_MODE_XL
  static constexpr uint8_t kCtrl9XlFastSettl = (1 << 5);  // XL_FASTSETTL_MODE
  static constexpr uint8_t kCtrl9HpSlopeXlEn = (1 << 4);  // HP_SLOPE_XL_EN (1 = HP path)
  static constexpr uint8_t kCtrl9Lpf2XlEn    = (1 << 3);  // LPF2_XL_EN (high-resolution)

  enum class AccelHpfOdr : uint8_t {
    kHpf4mHz    = 0x00,
    kHpf260mHz  = 0x01,
    kHpf1Hz04   = 0x02,
    kHpf4Hz16   = 0x03,
    kHpf8Hz30   = 0x04,
    kHpf16Hz32  = 0x05,
  };

  enum class AccelLpf2Odr : uint8_t {
    kLpf2OdrDiv4   = 0x00,
    kLpf2OdrDiv10  = 0x01,
    kLpf2OdrDiv20  = 0x02,
    kLpf2OdrDiv45  = 0x03,
    kLpf2OdrDiv100 = 0x04,
    kLpf2OdrDiv200 = 0x05,
    kLpf2OdrDiv400 = 0x06,
    kLpf2OdrDiv800 = 0x07,
  };

  // =========================================================================
  // MD1_CFG (0x5E) / MD2_CFG (0x5F) — Interrupt routing
  // =========================================================================
  static constexpr uint8_t kMdCfgInt6D        = (1 << 0);
  static constexpr uint8_t kMdCfgIntEmbFunc   = (1 << 1);  // EMB_FUNC_ENDOP → INTx
  static constexpr uint8_t kMdCfgIntDoubleTap = (1 << 3);
  static constexpr uint8_t kMdCfgIntFreeFall  = (1 << 4);
  static constexpr uint8_t kMdCfgIntWakeUp    = (1 << 5);
  static constexpr uint8_t kMdCfgIntSingleTap = (1 << 6);
  static constexpr uint8_t kMdCfgIntSleepChg  = (1 << 7);

  // =========================================================================
  // FUNC_CFG_ACCESS (0x01) — Bank / page access control
  // =========================================================================
  static constexpr uint8_t kFuncCfgEn         = (1 << 7);  // 1 = embedded fn registers
  static constexpr uint8_t kShubRegAccess     = (1 << 6);  // 1 = sensor hub registers

  // EMB_FUNC_EN_A (0x04 in emb bank)
  static constexpr uint8_t kEmbFuncEnASflp     = (1 << 1);  // SFLP_GAME_EN

  // INT2_CTRL (0x0E user bank) — INT2 signal routing
  static constexpr uint8_t kInt2CtrlEmbFuncEndop = (1 << 7);  // INT2_EMB_FUNC_ENDOP → INT2

  // SFLP_ODR (0x5E in emb bank) — SFLP game ODR in bits [5:3].
  // Bits 6, 1, 0 read as 1 and must be preserved when writing (see kSflpOdrFixed).
  enum class SflpOdr : uint8_t {
    kOdr15Hz  = (0 << 3),
    kOdr30Hz  = (1 << 3),
    kOdr60Hz  = (2 << 3),
    kOdr120Hz = (3 << 3),
    kOdr240Hz = (4 << 3),
    kOdr480Hz = (5 << 3),
  };
  static constexpr uint8_t kSflpOdrMask  = 0x38;  // SFLP_GAME_ODR_[2:0]
  static constexpr uint8_t kSflpOdrFixed = 0x43;  // bits 6,1,0 read-as-1

  // EMB_FUNC_INIT_A (0x66 in emb bank) — SFLP re-initialise
  static constexpr uint8_t kEmbFuncInitASflpGameInit = (1 << 1);

  // PAGE_RW (0x17 in emb bank during page access) bit masks
  static constexpr uint8_t kPageRwRead  = (1 << 5);  // PAGE_READ
  static constexpr uint8_t kPageRwWrite = (1 << 6);  // PAGE_WRITE

  // PAGE_SEL (0x02) — page number in the high nibble [7:4]; bit0 reads as 1.
  static constexpr uint8_t kPageSelFixed   = 0x01;  // bit0 must be written 1
  static constexpr uint8_t kPageNumShift   = 4;     // page number occupies bits [7:4]

  // =========================================================================
  // STATUS_REG (0x1E) — Data ready flags
  // =========================================================================
  static constexpr uint8_t kStatusXlda  = (1 << 0);  // Accelerometer data ready
  static constexpr uint8_t kStatusGda   = (1 << 1);  // Gyroscope data ready
  static constexpr uint8_t kStatusTda   = (1 << 2);  // Temperature data ready

  // =========================================================================
  // FIFO_CTRL4 (0x0A) — FIFO mode
  // =========================================================================
  enum class FifoMode : uint8_t {
    kBypass       = 0x00,
    kFifo         = 0x01,
    kContinuousToFifo = 0x03,
    kBypassToContinuous = 0x04,
    kContinuous   = 0x06,
    kBypassToFifo = 0x07,
  };

  // FIFO batch data rates for accel / gyro (FIFO_CTRL3, 0x09)
  enum class FifoBdr : uint8_t {
    kBdrOff   = 0x00,
    kBdr1Hz875 = 0x01,
    kBdr7Hz5  = 0x02,
    kBdr15Hz  = 0x03,
    kBdr30Hz  = 0x04,
    kBdr60Hz  = 0x05,
    kBdr120Hz = 0x06,
    kBdr240Hz = 0x07,
    kBdr480Hz = 0x08,
    kBdr960Hz = 0x09,
    kBdr1920Hz = 0x0A,
    kBdr3840Hz = 0x0B,
    kBdr7680Hz = 0x0C,
  };

  // =========================================================================
  // Embedded advanced features — page 3 quaternion register base
  // =========================================================================
  // Undocumented full-precision workaround (per ST community forum / ST FAE PoC):
  // all 4 components are stored as FP16, 2 bytes each, at 0x4C–0x53 on page 3.
  // Byte order from base 0x4C is W, X, Y, Z (Qw_L at 0x4C). Read one byte at a
  // time via PAGE_ADDRESS/PAGE_VALUE. PAGE_SEL is written as (3 << 4) | 1 = 0x31.
  static constexpr uint8_t kAdvPageQuat      = 3;     // Embedded advanced features page
  static constexpr uint8_t kAdvRegQuatBase   = 0x4C;  // Qw_L, first byte (W component)

  // =========================================================================
  // Sensitivity constants (per datasheet Table 2)
  // =========================================================================
  // Accel: mg/LSB for each full-scale range.
  static constexpr float kAccelSens2g  = 0.061f;
  static constexpr float kAccelSens4g  = 0.122f;
  static constexpr float kAccelSens8g  = 0.244f;
  static constexpr float kAccelSens16g = 0.488f;

  // Gyro: mdps/LSB for each full-scale range.
  static constexpr float kGyroSens125dps  = 4.375f;
  static constexpr float kGyroSens250dps  = 8.750f;
  static constexpr float kGyroSens500dps  = 17.500f;
  static constexpr float kGyroSens1000dps = 35.000f;
  static constexpr float kGyroSens2000dps = 70.000f;
  static constexpr float kGyroSens4000dps = 140.000f;

  // Temperature: 1/256 °C per LSB, offset at 0 LSB = 25 °C.
  static constexpr float kTempSensitivity = 1.0f / 256.0f;
  static constexpr float kTempOffset      = 25.0f;

  // =========================================================================
  // Configuration — passed to the constructor.
  // =========================================================================
  struct Config {
    // SPI host this device lives on.
    spi_host_device_t spi_host = bsp.periph_spi_handle;

    // Pin configuration used when Init(true) initialises the bus.
    gpio_num_t mosi_pin        = bsp.periph_spi_mosi_pin;
    gpio_num_t miso_pin        = bsp.periph_spi_miso_pin;
    gpio_num_t clk_pin         = bsp.periph_spi_clk_pin;
    int        max_transfer_sz = bsp.periph_spi_max_transfer_sz;

    // GPIO used as chip-select (hardware-managed by the SPI driver).
    gpio_num_t cs_pin = bsp.periph_spi_imu_cs_pin;

    // GPIO connected to the sensor INT2 pin.  Must support edge interrupts.
    // The driver installs an ISR on this pin; the application must call
    // gpio_install_isr_service() before calling Init().
    gpio_num_t int2_pin = bsp.periph_spi_imu_int2_pin;

    // SPI clock frequency (Hz).  The LSM6DSV supports up to 10 MHz.
    int spi_clock_hz = 10000000;

    // Reader task stack and priority. The task sits blocked on INT2 and
    // performs the quaternion page read immediately on notification.
    // Priority should be above the main loop to preempt it on interrupt.
    uint32_t reader_task_stack  = 4096;
    UBaseType_t reader_task_priority = tskIDLE_PRIORITY + 2;

    // Sensor fusion (SFLP) settings. 30 Hz keeps the page-3 quaternion update
    // window wide (~33 ms) so the INT2 reader task can finish its 21-transaction
    // read cleanly between updates even while the EPD contends for the shared SPI
    // bus (avoids torn FP16 reads → NaN).
    SflpOdr sflp_odr = SflpOdr::kOdr30Hz;

    // Accelerometer settings.
    AccelOdr  accel_odr  = AccelOdr::kOdr7680Hz;
    AccelFs   accel_fs   = AccelFs::kFs8g;
    AccelMode accel_mode = AccelMode::kHighPerformance;

    // Gyroscope settings.
    GyroOdr  gyro_odr  = GyroOdr::kOdr7680Hz;
    GyroFs   gyro_fs   = GyroFs::kFs1000dps;
    GyroMode gyro_mode = GyroMode::kHighPerformance;
  };

  // =========================================================================
  // Measurement data — populated by Update()
  // =========================================================================
  // NOTE: glm types are default-uninitialized; the explicit member initializers
  // here are REQUIRED so ImuData{} yields identity/zero, not garbage.
  struct ImuData {
    glm::vec3 accel_mg{0.0f};   // Acceleration in milli-g (x, y, z)
    glm::vec3 gyro_mdps{0.0f};  // Angular rate in milli-degrees per second (x, y, z)
    float temperature_c = 0.0f;
    glm::quat quaternion{1.0f, 0.0f, 0.0f, 0.0f};  // identity (w, x, y, z)
    bool quaternion_valid = false;  // True after first INT2_EMB_FUNC_ENDOP
  };

  Lsm6dsv() : Lsm6dsv(Config{}) {}
  explicit Lsm6dsv(const Config& config);
  ~Lsm6dsv();

  Lsm6dsv(const Lsm6dsv&)             = delete;
  Lsm6dsv& operator=(const Lsm6dsv&)  = delete;

  // =========================================================================
  // Lifecycle
  // =========================================================================

  // Adds the device to the SPI bus, verifies WHO_AM_I, issues a software
  // reset, configures all registers per the Config struct, enables the SFLP
  // embedded function, spawns the reader task, and installs the INT2 ISR.
  // Pass init_spi_bus=true for the first device on the bus; subsequent
  // devices sharing the same bus should pass false.
  bool Init(bool init_spi_bus = false);

  // Removes the device from the SPI bus, stops the reader task, and
  // uninstalls the INT2 ISR.
  bool Deinit();

  bool IsInitialized() const { return spi_handle_ != nullptr; }

  // =========================================================================
  // Sensor control (call only after Init())
  // =========================================================================

  // Reads raw accel/gyro/temp registers (14-byte burst). The quaternion is
  // updated asynchronously by the reader task on each INT2 interrupt.
  bool Update();

  // Issues a software reset; re-runs full configuration afterwards.
  bool SoftReset();

  // Change accelerometer ODR / full-scale / mode at runtime.
  bool SetAccelConfig(AccelOdr odr, AccelFs fs, AccelMode mode);

  // Change gyroscope ODR / full-scale / mode at runtime.
  bool SetGyroConfig(GyroOdr odr, GyroFs fs, GyroMode mode);

  // Change SFLP output data rate at runtime.
  bool SetSflpOdr(SflpOdr odr);

  // Re-initialise the SFLP algorithm (equivalent to writing SFLP_GAME_INIT).
  bool ResetSflp();

  // Enable or disable block data update (BDU).
  bool SetBdu(bool enable);

  // Set gyroscope LPF1 bandwidth.
  bool SetGyroLpf1Bw(GyroLpf1Bw bw);

  // Set accelerometer LPF2 and high-pass filter configuration.
  bool SetAccelFilterConfig(bool lpf2_enable, AccelLpf2Odr lpf2_odr,
                             bool hpf_enable, AccelHpfOdr hpf_odr);

  // Set FIFO mode and accel/gyro batch data rates.
  bool SetFifoConfig(FifoMode mode, FifoBdr accel_bdr, FifoBdr gyro_bdr);

  // Configure INT1 signal routing.  Pass a bitmask of kMdCfgInt* constants.
  bool SetInt1Routing(uint8_t mask);

  // Configure INT2 signal routing.  Pass a bitmask of kMdCfgInt* constants.
  // Note: kMdCfgIntEmbFunc is automatically set by Init(); do not clear it.
  bool SetInt2Routing(uint8_t mask);

  // Enable or disable the I2C/I3C interface (keep disabled when using SPI).
  bool SetI2cDisabled(bool disable);

  // =========================================================================
  // Getters — always safe to call; return last successfully decoded values.
  // =========================================================================
  const ImuData& GetData() const { return data_; }

  // GLM-native vector getters (preferred).
  const glm::vec3& GetAccelMg()  const { return data_.accel_mg; }
  const glm::vec3& GetGyroMdps() const { return data_.gyro_mdps; }

  // Scalar getters retained for source compatibility; forward to the vec3 fields.
  float GetAccelXMg()     const { return data_.accel_mg.x; }
  float GetAccelYMg()     const { return data_.accel_mg.y; }
  float GetAccelZMg()     const { return data_.accel_mg.z; }
  float GetGyroXMdps()    const { return data_.gyro_mdps.x; }
  float GetGyroYMdps()    const { return data_.gyro_mdps.y; }
  float GetGyroZMdps()    const { return data_.gyro_mdps.z; }
  float GetTemperatureC() const { return data_.temperature_c; }
  const glm::quat& GetQuaternion() const { return data_.quaternion; }
  bool  IsQuaternionValid() const { return data_.quaternion_valid; }

 private:
  // Acquire/release the shared SPI bus around multi-transaction IMU sequences so
  // they are atomic with respect to the EPD (same host). Mirrors the EPD driver.
  void AcquireBus();
  void ReleaseBus();

  // SPI register access helpers.
  esp_err_t WriteRegister(Register reg, uint8_t value);
  esp_err_t WriteRegister(uint8_t reg_addr, uint8_t value);  // Raw address overload.
  esp_err_t ReadRegister(Register reg, uint8_t* value);
  esp_err_t ReadRegisters(Register start_reg, uint8_t* buf, size_t len);

  // Embedded function bank access (sets/clears FUNC_CFG_EN).
  esp_err_t WriteEmbRegister(Register reg, uint8_t value);
  esp_err_t ReadEmbRegister(Register reg, uint8_t* value);
  esp_err_t ModifyEmbRegister(Register reg, uint8_t mask, uint8_t value);

  // Full page-3 quaternion readout (21 individual SPI transactions).
  // Must be called only after INT2_EMB_FUNC_ENDOP and before the next ODR.
  esp_err_t ReadQuaternionFromPage(uint8_t buf[8]);

  // Decode raw accel/gyro/temp registers into data_.
  void DecodeImu(const uint8_t raw[14]);

  // Normalise four FP16 quaternion components and store into data_.quaternion.
  void DecodeAndNormalizeQuaternion(const uint8_t raw[8]);

  // Apply all settings from config_ to the device.
  bool ApplyConfig();

  // Configure the SFLP embedded function (embedded bank).
  bool ConfigureSflp();

  // Return the accel sensitivity (mg/LSB) for the current full-scale setting.
  float AccelSensitivity() const;

  // Return the gyro sensitivity (mdps/LSB) for the current full-scale setting.
  float GyroSensitivity() const;

  // Help convert float16 (not supported by platform) to float32
  float Float16ToFloat32(uint16_t h);

  // INT2 ISR — notifies reader_task_ directly for minimum latency.
  static void IRAM_ATTR Int2IsrHandler(void* arg);

  // Reader task — blocks on task notification, then immediately performs
  // the quaternion page read sequence and updates data_.quaternion.
  static void ReaderTask(void* arg);

  const Config config_;

  spi_device_handle_t spi_handle_      = nullptr;
  bool                owned_spi_bus_  = false;
  TaskHandle_t        reader_task_    = nullptr;

  // Shadow of current full-scale settings (needed for sensitivity lookup).
  AccelFs accel_fs_ = AccelFs::kFs8g;
  GyroFs  gyro_fs_  = GyroFs::kFs1000dps;

  // Last successfully decoded measurement values.
  ImuData data_ = {};
};
