#include "lsm6dsv.hh"

#include <cmath>
#include <cstring>
#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

static const char* kTag = "LSM6DSV";

// SPI frame: bit7 = 1 → read, bit7 = 0 → write.
// LSM6DSV uses SPI Mode 3 (CPOL=1, CPHA=1) per datasheet §7.2.
static constexpr uint8_t kSpiReadFlag  = 0x80;
static constexpr uint8_t kSpiWriteFlag = 0x00;

// ---------------------------------------------------------------------------
// Constructor / Destructor
// ---------------------------------------------------------------------------

Lsm6dsv::Lsm6dsv(const Config& config)
    : config_(config),
      spi_handle_(nullptr),
      reader_task_(nullptr),
      accel_fs_(config.accel_fs),
      gyro_fs_(config.gyro_fs),
      data_() {}

Lsm6dsv::~Lsm6dsv() {
  if (spi_handle_ != nullptr) {
    Deinit();
  }
}

// ---------------------------------------------------------------------------
// Lifecycle
// ---------------------------------------------------------------------------

bool Lsm6dsv::Init(bool init_spi_bus) {  // NOLINT: default in header
  if (spi_handle_ != nullptr) {
    ESP_LOGW(kTag, "Already initialized — call Deinit() first");
    return false;
  }

  if (init_spi_bus) {
    spi_bus_config_t bus_cfg = {};
    bus_cfg.mosi_io_num     = config_.mosi_pin;
    bus_cfg.miso_io_num     = config_.miso_pin;
    bus_cfg.sclk_io_num     = config_.clk_pin;
    bus_cfg.quadwp_io_num   = -1;
    bus_cfg.quadhd_io_num   = -1;
    bus_cfg.max_transfer_sz = config_.max_transfer_sz;
    esp_err_t ret = spi_bus_initialize(config_.spi_host, &bus_cfg, SPI_DMA_CH_AUTO);
    if (ret != ESP_OK) {
      ESP_LOGE(kTag, "Failed to initialize SPI bus: %s", esp_err_to_name(ret));
      return false;
    }
    owned_spi_bus_ = true;
    ESP_LOGI(kTag, "Initialized SPI bus on host %d", config_.spi_host);
  }

  // Add device to the SPI bus.
  // Use hardware CS and SPI Mode 3 (CPOL=1, CPHA=1) matching the PoC.
  spi_device_interface_config_t dev_cfg = {};
  dev_cfg.mode           = 3;
  dev_cfg.clock_speed_hz = config_.spi_clock_hz;
  dev_cfg.spics_io_num   = config_.cs_pin;
  dev_cfg.queue_size     = 1;

  esp_err_t ret = spi_bus_add_device(config_.spi_host, &dev_cfg, &spi_handle_);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to add SPI device: %s", esp_err_to_name(ret));
    spi_handle_ = nullptr;
    return false;
  }

  vTaskDelay(pdMS_TO_TICKS(10));

  // Verify device identity.
  uint8_t who_am_i = 0;
  ret = ReadRegister(kRegWhoAmI, &who_am_i);
  if (ret != ESP_OK || who_am_i != kWhoAmIValue) {
    ESP_LOGE(kTag, "WHO_AM_I failed: got 0x%02X, expected 0x%02X",
             who_am_i, kWhoAmIValue);
    Deinit();
    return false;
  }

  if (!ApplyConfig()) {
    Deinit();
    return false;
  }

  // Spawn the reader task before enabling the ISR so reader_task_ is valid
  // when the first notification arrives.
  xTaskCreate(ReaderTask, "lsm6dsv_reader", config_.reader_task_stack,
              this, config_.reader_task_priority, &reader_task_);
  if (reader_task_ == nullptr) {
    ESP_LOGE(kTag, "Failed to create reader task");
    Deinit();
    return false;
  }

  // Configure INT2 and install ISR last.
  gpio_config_t int2_cfg = {};
  int2_cfg.pin_bit_mask = 1ULL << config_.int2_pin;
  int2_cfg.mode         = GPIO_MODE_INPUT;
  int2_cfg.pull_up_en   = GPIO_PULLUP_DISABLE;
  int2_cfg.pull_down_en = GPIO_PULLDOWN_ENABLE;
  int2_cfg.intr_type    = GPIO_INTR_POSEDGE;
  ret = gpio_config(&int2_cfg);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to configure INT2 pin: %s", esp_err_to_name(ret));
    Deinit();
    return false;
  }

  ret = gpio_isr_handler_add(config_.int2_pin, Int2IsrHandler, this);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to install INT2 ISR: %s", esp_err_to_name(ret));
    Deinit();
    return false;
  }

  ESP_LOGI(kTag, "Initialized. WHO_AM_I=0x%02X", who_am_i);
  return true;
}

bool Lsm6dsv::Deinit() {
  if (spi_handle_ == nullptr) {
    return true;
  }

  gpio_isr_handler_remove(config_.int2_pin);
  gpio_set_intr_type(config_.int2_pin, GPIO_INTR_DISABLE);

  if (reader_task_ != nullptr) {
    vTaskDelete(reader_task_);
    reader_task_ = nullptr;
  }

  bool ok = true;
  esp_err_t ret = spi_bus_remove_device(spi_handle_);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to remove SPI device: %s", esp_err_to_name(ret));
    ok = false;
  }
  spi_handle_ = nullptr;
  ESP_LOGI(kTag, "Deinitialized");
  return ok;
}

// ---------------------------------------------------------------------------
// Sensor control
// ---------------------------------------------------------------------------

bool Lsm6dsv::SoftReset() {
  esp_err_t ret = WriteRegister(kRegCtrl3, kCtrl3SwReset);
  if (ret != ESP_OK) return false;

  const uint32_t kTimeoutMs = 50;
  const uint32_t kPollMs    = 2;
  uint32_t elapsed = 0;
  while (elapsed < kTimeoutMs) {
    vTaskDelay(pdMS_TO_TICKS(kPollMs));
    elapsed += kPollMs;
    uint8_t ctrl3 = 0;
    ret = ReadRegister(kRegCtrl3, &ctrl3);
    if (ret != ESP_OK) return false;
    if (!(ctrl3 & kCtrl3SwReset)) break;
  }
  if (elapsed >= kTimeoutMs) {
    ESP_LOGE(kTag, "Software reset timed out");
    return false;
  }
  ret = WriteRegister(kRegCtrl3, kCtrl3IfInc | kCtrl3Bdu);
  if (ret != ESP_OK) return false;

  data_.quaternion_valid = false;
  return true;
}

bool Lsm6dsv::SetAccelConfig(AccelOdr odr, AccelFs fs, AccelMode mode) {
  // CTRL1 = [0][OP_MODE_XL_2:0][ODR_XL_3:0]; full-scale lives in CTRL8 (FS_XL).
  uint8_t ctrl1 = ((static_cast<uint8_t>(mode) & 0x07) << 4) |
                   (static_cast<uint8_t>(odr) & 0x0F);
  if (WriteRegister(kRegCtrl1, ctrl1) != ESP_OK) return false;

  uint8_t ctrl8 = 0;
  if (ReadRegister(kRegCtrl8, &ctrl8) != ESP_OK) return false;
  ctrl8 = (ctrl8 & ~kCtrl8FsXlMask) | (static_cast<uint8_t>(fs) & kCtrl8FsXlMask);
  if (WriteRegister(kRegCtrl8, ctrl8) != ESP_OK) return false;

  accel_fs_ = fs;
  return true;
}

bool Lsm6dsv::SetGyroConfig(GyroOdr odr, GyroFs fs, GyroMode mode) {
  // CTRL2 = [0][OP_MODE_G_2:0][ODR_G_3:0]; full-scale lives in CTRL6 (FS_G).
  uint8_t ctrl2 = ((static_cast<uint8_t>(mode) & 0x07) << 4) |
                   (static_cast<uint8_t>(odr) & 0x0F);
  if (WriteRegister(kRegCtrl2, ctrl2) != ESP_OK) return false;

  uint8_t ctrl6 = 0;
  if (ReadRegister(kRegCtrl6, &ctrl6) != ESP_OK) return false;
  ctrl6 = (ctrl6 & ~kCtrl6FsGMask) | (static_cast<uint8_t>(fs) & kCtrl6FsGMask);
  if (WriteRegister(kRegCtrl6, ctrl6) != ESP_OK) return false;

  gyro_fs_ = fs;
  return true;
}

bool Lsm6dsv::SetSflpOdr(SflpOdr odr) {
  // SFLP_ODR (0x5E, emb bank): write the game-ODR field while keeping the
  // read-as-1 bits (6,1,0) set, as ModifyEmbRegister only touches the masked bits.
  return ModifyEmbRegister(kRegSflpOdr, kSflpOdrMask | kSflpOdrFixed,
                            static_cast<uint8_t>(odr) | kSflpOdrFixed) == ESP_OK;
}

bool Lsm6dsv::ResetSflp() {
  return ModifyEmbRegister(kRegEmbFuncInitA, kEmbFuncInitASflpGameInit,
                            kEmbFuncInitASflpGameInit) == ESP_OK;
}

bool Lsm6dsv::SetBdu(bool enable) {
  uint8_t ctrl3 = 0;
  if (ReadRegister(kRegCtrl3, &ctrl3) != ESP_OK) return false;
  if (enable) { ctrl3 |= kCtrl3Bdu; } else { ctrl3 &= ~kCtrl3Bdu; }
  return WriteRegister(kRegCtrl3, ctrl3) == ESP_OK;
}

bool Lsm6dsv::SetGyroLpf1Bw(GyroLpf1Bw bw) {
  // LPF1_G_BW_[2:0] occupies CTRL6 bits [6:4]; preserve FS_G in bits [3:0].
  uint8_t ctrl6 = 0;
  if (ReadRegister(kRegCtrl6, &ctrl6) != ESP_OK) return false;
  ctrl6 = (ctrl6 & ~kCtrl6Lpf1BwMask) |
          ((static_cast<uint8_t>(bw) << 4) & kCtrl6Lpf1BwMask);
  return WriteRegister(kRegCtrl6, ctrl6) == ESP_OK;
}

bool Lsm6dsv::SetAccelFilterConfig(bool lpf2_enable, AccelLpf2Odr lpf2_odr,
                                    bool hpf_enable, AccelHpfOdr hpf_odr) {
  // The bandwidth code sits in CTRL8[7:5] (HP_LPF2_XL_BW); whether it is a
  // low-pass (LPF2) or high-pass (slope) filter is selected by the enable bits
  // in CTRL9.  The two ODR enums share the same 3-bit code space (Table 68).
  uint8_t bw_code = hpf_enable ? static_cast<uint8_t>(hpf_odr)
                               : static_cast<uint8_t>(lpf2_odr);

  uint8_t ctrl8 = 0;
  if (ReadRegister(kRegCtrl8, &ctrl8) != ESP_OK) return false;
  ctrl8 = (ctrl8 & ~kCtrl8BwMask) | ((bw_code << 5) & kCtrl8BwMask);
  if (WriteRegister(kRegCtrl8, ctrl8) != ESP_OK) return false;

  uint8_t ctrl9 = 0;
  if (ReadRegister(kRegCtrl9, &ctrl9) != ESP_OK) return false;
  ctrl9 &= ~(kCtrl9Lpf2XlEn | kCtrl9HpSlopeXlEn);
  if (lpf2_enable) ctrl9 |= kCtrl9Lpf2XlEn;
  if (hpf_enable)  ctrl9 |= kCtrl9HpSlopeXlEn;
  return WriteRegister(kRegCtrl9, ctrl9) == ESP_OK;
}

bool Lsm6dsv::SetFifoConfig(FifoMode mode, FifoBdr accel_bdr, FifoBdr gyro_bdr) {
  uint8_t ctrl3 = (static_cast<uint8_t>(gyro_bdr)  << 4) |
                   static_cast<uint8_t>(accel_bdr);
  if (WriteRegister(kRegFifoCtrl3, ctrl3) != ESP_OK) return false;
  uint8_t ctrl4 = 0;
  if (ReadRegister(kRegFifoCtrl4, &ctrl4) != ESP_OK) return false;
  ctrl4 = (ctrl4 & 0xF8) | (static_cast<uint8_t>(mode) & 0x07);
  return WriteRegister(kRegFifoCtrl4, ctrl4) == ESP_OK;
}

bool Lsm6dsv::SetInt1Routing(uint8_t mask) {
  return WriteRegister(kRegMd1Cfg, mask) == ESP_OK;
}

bool Lsm6dsv::SetInt2Routing(uint8_t mask) {
  return WriteRegister(kRegMd2Cfg, mask | kMdCfgIntEmbFunc) == ESP_OK;
}

bool Lsm6dsv::SetI2cDisabled(bool disable) {
  // I2C_I3C_disable is IF_CFG (0x03) bit 0, not a CTRL4 bit.
  uint8_t if_cfg = 0;
  if (ReadRegister(kRegIfCfg, &if_cfg) != ESP_OK) return false;
  if (disable) { if_cfg |= kIfCfgI2cI3cDisable; }
  else         { if_cfg &= ~kIfCfgI2cI3cDisable; }
  return WriteRegister(kRegIfCfg, if_cfg) == ESP_OK;
}

// ---------------------------------------------------------------------------
// Update — reads raw accel/gyro/temp; quaternion updated by reader task
// ---------------------------------------------------------------------------

bool Lsm6dsv::Update() {
  uint8_t raw[14] = {};
  esp_err_t ret = ReadRegisters(kRegOutTempL, raw, sizeof(raw));
  if (ret != ESP_OK) {
    ESP_LOGW(kTag, "IMU burst read failed: %s", esp_err_to_name(ret));
    return false;
  }
  DecodeImu(raw);
  return true;
}

// ---------------------------------------------------------------------------
// Reader task — runs at elevated priority, woken by INT2 ISR
// ---------------------------------------------------------------------------

void Lsm6dsv::ReaderTask(void* arg) {
  Lsm6dsv* self = static_cast<Lsm6dsv*>(arg);
  uint32_t isr_count = 0;
  while (true) {
    ulTaskNotifyTake(pdTRUE, portMAX_DELAY);
    isr_count++;
    uint8_t quat_raw[8] = {};
    esp_err_t ret = self->ReadQuaternionFromPage(quat_raw);
    // ESP_LOGI(kTag, "INT2 #%lu page_read=%s raw=%02X%02X %02X%02X %02X%02X %02X%02X",
    //          isr_count, (ret == ESP_OK) ? "ok" : esp_err_to_name(ret),
    //          quat_raw[0], quat_raw[1], quat_raw[2], quat_raw[3],
    //          quat_raw[4], quat_raw[5], quat_raw[6], quat_raw[7]);
    if (ret == ESP_OK) {
      self->DecodeAndNormalizeQuaternion(quat_raw);
    }
  }
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

bool Lsm6dsv::ApplyConfig() {
  esp_err_t ret;

  // Follows the ST FAE PoC sequence, with register semantics corrected against
  // the datasheet (FS in CTRL6/CTRL8, ENDOP routing via INT2_CTRL, etc.).

  // 1. Enable SFLP and set its ODR in the embedded bank.
  if (!ConfigureSflp()) return false;

  // 2. CTRL4 = DRDY_MASK (mask DRDY until the filters have settled).
  ret = WriteRegister(kRegCtrl4, kCtrl4DrdyMask);
  if (ret != ESP_OK) return false;

  // 3. Gyroscope full-scale → CTRL6 (FS_G[3:0]); accel full-scale → CTRL8 (FS_XL).
  ret = WriteRegister(kRegCtrl6, static_cast<uint8_t>(config_.gyro_fs) & kCtrl6FsGMask);
  if (ret != ESP_OK) return false;
  ret = WriteRegister(kRegCtrl8, static_cast<uint8_t>(config_.accel_fs) & kCtrl8FsXlMask);
  if (ret != ESP_OK) return false;

  // 4. EMB_FUNC_CFG (0x63): mask the XL/GY settling interrupts (PoC value 0x30).
  ret = WriteRegister(kRegEmbFuncCfg, 0x30);
  if (ret != ESP_OK) return false;

  // 5. CTRL1 / CTRL2 — operating mode [6:4] + ODR [3:0].
  ret = WriteRegister(kRegCtrl1,
                      ((static_cast<uint8_t>(config_.accel_mode) & 0x07) << 4) |
                       (static_cast<uint8_t>(config_.accel_odr) & 0x0F));
  if (ret != ESP_OK) return false;
  ret = WriteRegister(kRegCtrl2,
                      ((static_cast<uint8_t>(config_.gyro_mode) & 0x07) << 4) |
                       (static_cast<uint8_t>(config_.gyro_odr) & 0x0F));
  if (ret != ESP_OK) return false;

  // 6. Route the SFLP end-of-operation interrupt to INT2 (INT2_CTRL bit 7).
  ret = WriteRegister(kRegInt2Ctrl, kInt2CtrlEmbFuncEndop);
  if (ret != ESP_OK) return false;

  accel_fs_ = config_.accel_fs;
  gyro_fs_  = config_.gyro_fs;
  return true;
}

bool Lsm6dsv::ConfigureSflp() {
  // Open the embedded bank, enable the SFLP game-rotation-vector function, set
  // its ODR (preserving SFLP_ODR's read-as-1 bits), then close the bank.
  esp_err_t ret = WriteRegister(kRegFuncCfgAccess, kFuncCfgEn);
  if (ret != ESP_OK) return false;

  ret = WriteEmbRegister(kRegEmbFuncEnA, kEmbFuncEnASflp);
  if (ret != ESP_OK) { WriteRegister(kRegFuncCfgAccess, 0); return false; }

  ret = WriteEmbRegister(kRegSflpOdr,
                         static_cast<uint8_t>(config_.sflp_odr) | kSflpOdrFixed);
  if (ret != ESP_OK) { WriteRegister(kRegFuncCfgAccess, 0); return false; }

  return WriteRegister(kRegFuncCfgAccess, 0) == ESP_OK;
}

esp_err_t Lsm6dsv::ReadQuaternionFromPage(uint8_t buf[8]) {
  // Embedded advanced features page read sequence (ST workaround):
  //   0x01 = 0x80  — enter embedded-functions bank (FUNC_CFG_EN)
  //   0x17 = 0x20  — assert PAGE_RW read enable (PAGE_READ)
  //   0x02 = 0x31  — select advanced features page 3 (page in [7:4], bit0=1)
  //   loop: write address to 0x08 (PAGE_ADDRESS), read byte from 0x09 (PAGE_VALUE)
  //   0x17 = 0x00  — deassert PAGE_RW
  //   0x01 = 0x00  — return to user bank

  esp_err_t ret = WriteRegister(kRegFuncCfgAccess, kFuncCfgEn);
  if (ret != ESP_OK) return ret;

  ret = WriteRegister(kRegPageRw, kPageRwRead);
  if (ret != ESP_OK) { WriteRegister(kRegFuncCfgAccess, 0); return ret; }

  ret = WriteRegister(kRegPageSel,
                      (kAdvPageQuat << kPageNumShift) | kPageSelFixed);
  if (ret != ESP_OK) {
    WriteRegister(kRegPageRw, 0);
    WriteRegister(kRegFuncCfgAccess, 0);
    return ret;
  }

  // Read 8 bytes (4 × FP16): order from PoC is x, y, z, w (base address 0x4C).
  for (uint8_t i = 0; i < 8; i++) {
    ret = WriteRegister(kRegPageAddress,
                        static_cast<uint8_t>(kAdvRegQuatBase + i));
    if (ret != ESP_OK) {
      WriteRegister(kRegPageRw, 0);
      WriteRegister(kRegFuncCfgAccess, 0);
      return ret;
    }
    ret = ReadRegister(kRegPageValue, &buf[i]);
    if (ret != ESP_OK) {
      WriteRegister(kRegPageRw, 0);
      WriteRegister(kRegFuncCfgAccess, 0);
      return ret;
    }
  }

  ret = WriteRegister(kRegPageRw, 0);
  if (ret != ESP_OK) { WriteRegister(kRegFuncCfgAccess, 0); return ret; }

  return WriteRegister(kRegFuncCfgAccess, 0);
}

void Lsm6dsv::DecodeImu(const uint8_t raw[14]) {
  // Byte layout from kRegOutTempL (0x20) with auto-increment:
  // [0-1] TEMP, [2-3] GX, [4-5] GY, [6-7] GZ, [8-9] AX, [10-11] AY, [12-13] AZ
  int16_t temp_raw = static_cast<int16_t>(static_cast<uint16_t>(raw[1])  << 8 | raw[0]);
  int16_t gx_raw   = static_cast<int16_t>(static_cast<uint16_t>(raw[3])  << 8 | raw[2]);
  int16_t gy_raw   = static_cast<int16_t>(static_cast<uint16_t>(raw[5])  << 8 | raw[4]);
  int16_t gz_raw   = static_cast<int16_t>(static_cast<uint16_t>(raw[7])  << 8 | raw[6]);
  int16_t ax_raw   = static_cast<int16_t>(static_cast<uint16_t>(raw[9])  << 8 | raw[8]);
  int16_t ay_raw   = static_cast<int16_t>(static_cast<uint16_t>(raw[11]) << 8 | raw[10]);
  int16_t az_raw   = static_cast<int16_t>(static_cast<uint16_t>(raw[13]) << 8 | raw[12]);

  data_.temperature_c = kTempOffset + static_cast<float>(temp_raw) * kTempSensitivity;

  const float asens   = AccelSensitivity();
  data_.accel_x_mg    = static_cast<float>(ax_raw) * asens;
  data_.accel_y_mg    = static_cast<float>(ay_raw) * asens;
  data_.accel_z_mg    = static_cast<float>(az_raw) * asens;

  const float gsens   = GyroSensitivity();
  data_.gyro_x_mdps   = static_cast<float>(gx_raw) * gsens;
  data_.gyro_y_mdps   = static_cast<float>(gy_raw) * gsens;
  data_.gyro_z_mdps   = static_cast<float>(gz_raw) * gsens;
}

void Lsm6dsv::DecodeAndNormalizeQuaternion(const uint8_t raw[8]) {
  // Component order from base 0x4C is w, x, y, z (PoC: sflp[0] is the scalar w):
  //   raw[0-1]=w, raw[2-3]=x, raw[4-5]=y, raw[6-7]=z, each FP16 little-endian.
  uint16_t bw = static_cast<uint16_t>(raw[1]) << 8 | raw[0];
  uint16_t bx = static_cast<uint16_t>(raw[3]) << 8 | raw[2];
  uint16_t by = static_cast<uint16_t>(raw[5]) << 8 | raw[4];
  uint16_t bz = static_cast<uint16_t>(raw[7]) << 8 | raw[6];

  float w = Float16ToFloat32(bw);
  float x = Float16ToFloat32(bx);
  float y = Float16ToFloat32(by);
  float z = Float16ToFloat32(bz);

  float norm = sqrtf(w * w + x * x + y * y + z * z);
  if (norm > 1e-6f) {
    w /= norm; x /= norm; y /= norm; z /= norm;
  } else {
    w = 1.0f; x = 0.0f; y = 0.0f; z = 0.0f;
  }

  data_.quaternion       = { w, x, y, z };
  data_.quaternion_valid = true;
}

float Lsm6dsv::AccelSensitivity() const {
  switch (accel_fs_) {
    case AccelFs::kFs2g:  return kAccelSens2g;
    case AccelFs::kFs4g:  return kAccelSens4g;
    case AccelFs::kFs8g:  return kAccelSens8g;
    case AccelFs::kFs16g: return kAccelSens16g;
    default:              return kAccelSens8g;
  }
}

float Lsm6dsv::GyroSensitivity() const {
  switch (gyro_fs_) {
    case GyroFs::kFs125dps:  return kGyroSens125dps;
    case GyroFs::kFs250dps:  return kGyroSens250dps;
    case GyroFs::kFs500dps:  return kGyroSens500dps;
    case GyroFs::kFs1000dps: return kGyroSens1000dps;
    case GyroFs::kFs2000dps: return kGyroSens2000dps;
    case GyroFs::kFs4000dps: return kGyroSens4000dps;
    default:                 return kGyroSens1000dps;
  }
}

// ---------------------------------------------------------------------------
// SPI low-level helpers — use polling_transmit to match the working PoC
// ---------------------------------------------------------------------------

esp_err_t Lsm6dsv::WriteRegister(Register reg, uint8_t value) {
  spi_transaction_t t = {};
  t.length     = 16;
  t.flags      = SPI_TRANS_USE_TXDATA;
  t.tx_data[0] = kSpiWriteFlag | static_cast<uint8_t>(reg);
  t.tx_data[1] = value;
  return spi_device_polling_transmit(spi_handle_, &t);
}

esp_err_t Lsm6dsv::WriteRegister(uint8_t reg_addr, uint8_t value) {
  return WriteRegister(static_cast<Register>(reg_addr), value);
}

esp_err_t Lsm6dsv::ReadRegister(Register reg, uint8_t* value) {
  spi_transaction_t t = {};
  t.length    = 16;
  t.rxlength  = 16;
  t.flags     = SPI_TRANS_USE_TXDATA | SPI_TRANS_USE_RXDATA;
  t.tx_data[0] = kSpiReadFlag | static_cast<uint8_t>(reg);
  t.tx_data[1] = 0x00;
  esp_err_t ret = spi_device_polling_transmit(spi_handle_, &t);
  if (ret == ESP_OK) *value = t.rx_data[1];
  return ret;
}

esp_err_t Lsm6dsv::ReadRegisters(Register start_reg, uint8_t* buf, size_t len) {
  static constexpr size_t kMaxBurst = 32;
  if (len > kMaxBurst - 1) return ESP_ERR_INVALID_ARG;

  uint8_t tx[kMaxBurst] = {};
  uint8_t rx[kMaxBurst] = {};
  tx[0] = kSpiReadFlag | static_cast<uint8_t>(start_reg);

  spi_transaction_t t = {};
  t.length    = (1 + len) * 8;
  t.tx_buffer = tx;
  t.rx_buffer = rx;

  esp_err_t ret = spi_device_polling_transmit(spi_handle_, &t);
  if (ret == ESP_OK) memcpy(buf, rx + 1, len);
  return ret;
}

esp_err_t Lsm6dsv::WriteEmbRegister(Register reg, uint8_t value) {
  return WriteRegister(reg, value);
}

esp_err_t Lsm6dsv::ReadEmbRegister(Register reg, uint8_t* value) {
  return ReadRegister(reg, value);
}

esp_err_t Lsm6dsv::ModifyEmbRegister(Register reg, uint8_t mask, uint8_t value) {
  esp_err_t ret = WriteRegister(kRegFuncCfgAccess, kFuncCfgEn);
  if (ret != ESP_OK) return ret;

  uint8_t current = 0;
  ret = ReadEmbRegister(reg, &current);
  if (ret != ESP_OK) { WriteRegister(kRegFuncCfgAccess, 0); return ret; }

  current = (current & ~mask) | (value & mask);
  ret = WriteEmbRegister(reg, current);

  esp_err_t cleanup = WriteRegister(kRegFuncCfgAccess, 0);
  return (ret != ESP_OK) ? ret : cleanup;
}

float Lsm6dsv::Float16ToFloat32(uint16_t h) {
  uint32_t sign     = (h & 0x8000) >> 15;
  uint32_t exponent = (h & 0x7C00) >> 10;
  uint32_t mantissa = (h & 0x03FF);
  uint32_t f;

  if (exponent == 0) {
    if (mantissa == 0) {
      f = sign << 31;
    } else {
      exponent = 1;
      while ((mantissa & 0x0400) == 0) { mantissa <<= 1; exponent--; }
      mantissa &= 0x03FF;
      f = (sign << 31) | (((127 - 15) + exponent) << 23) | (mantissa << 13);
    }
  } else if (exponent == 0x1F) {
    f = (sign << 31) | (0xFF << 23) | (mantissa << 13);
  } else {
    f = (sign << 31) | ((exponent + (127 - 15)) << 23) | (mantissa << 13);
  }

  float result;
  __builtin_memcpy(&result, &f, sizeof(result));
  return result;
}

// ---------------------------------------------------------------------------
// INT2 ISR — notifies reader task with minimum latency
// ---------------------------------------------------------------------------

void IRAM_ATTR Lsm6dsv::Int2IsrHandler(void* arg) {
  Lsm6dsv* self = static_cast<Lsm6dsv*>(arg);
  BaseType_t higher_priority_task_woken = pdFALSE;
  vTaskNotifyGiveFromISR(self->reader_task_, &higher_priority_task_woken);
  portYIELD_FROM_ISR(higher_priority_task_woken);
}
