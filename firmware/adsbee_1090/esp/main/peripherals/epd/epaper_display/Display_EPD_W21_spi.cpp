#include "Display_EPD_W21_spi.hh"

#include <algorithm>
#include <cmath>

#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

static const char* kTag = "EPD";

// ---------------------------------------------------------------------------
// Constructor / Destructor
// ---------------------------------------------------------------------------

DisplayEpdW21::DisplayEpdW21(const Config& config)
    : config_(config), spi_handle_(nullptr), owned_spi_bus_(false) {}

DisplayEpdW21::~DisplayEpdW21() {
  if (spi_handle_ != nullptr) {
    Deinit();
  }
}

// ---------------------------------------------------------------------------
// Lifecycle
// ---------------------------------------------------------------------------

bool DisplayEpdW21::Init(bool init_spi_bus) {
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

  // Configure CS and DC as outputs.
  gpio_config_t out_cfg = {};
  out_cfg.mode          = GPIO_MODE_OUTPUT;
  out_cfg.pin_bit_mask  = (1ULL << config_.cs_pin) | (1ULL << config_.dc_pin);
  out_cfg.pull_up_en    = GPIO_PULLUP_DISABLE;
  out_cfg.pull_down_en  = GPIO_PULLDOWN_DISABLE;
  out_cfg.intr_type     = GPIO_INTR_DISABLE;
  esp_err_t ret = gpio_config(&out_cfg);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to configure CS/DC pins: %s", esp_err_to_name(ret));
    if (owned_spi_bus_) { spi_bus_free(config_.spi_host); owned_spi_bus_ = false; }
    return false;
  }
  gpio_set_level(config_.cs_pin, 1);
  gpio_set_level(config_.dc_pin, 1);

  // CS is driven manually so the SPI driver doesn't manage it (spics_io_num = -1).
  spi_device_interface_config_t dev_cfg = {};
  dev_cfg.clock_speed_hz = config_.spi_clock_hz;
  dev_cfg.mode           = 0;   // SSD1680A: CPOL=0, CPHA=0
  dev_cfg.spics_io_num   = -1;
  dev_cfg.queue_size     = 1;
  ret = spi_bus_add_device(config_.spi_host, &dev_cfg, &spi_handle_);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to add SPI device: %s", esp_err_to_name(ret));
    spi_handle_ = nullptr;
    if (owned_spi_bus_) { spi_bus_free(config_.spi_host); owned_spi_bus_ = false; }
    return false;
  }

  // Configure RST and BUSY on the GPIO expander.
  Fxl6408::ConfigurePin(config_.rst_pin,
      { Fxl6408::Direction::kOutput, Fxl6408::PullMode::kNone, true, false });
  Fxl6408::ConfigurePin(config_.busy_pin,
      { Fxl6408::Direction::kInput,  Fxl6408::PullMode::kNone, false, false });

  ApplyHwInit();

  // Configure the LED front light (PWM). Non-fatal if it fails — the display
  // still works without it.
  InitFrontLight();

  ESP_LOGI(kTag, "Initialized (CS:%d DC:%d)", config_.cs_pin, config_.dc_pin);
  return true;
}

bool DisplayEpdW21::Deinit() {
  if (spi_handle_ == nullptr) {
    return true;
  }

  bool ok = true;

  // Turn off the front light and release the LEDC channel.
  if (front_light_ready_) {
    ledc_stop(kFrontLightSpeedMode, kFrontLightChannel, 0);
    front_light_ready_ = false;
  }

  esp_err_t ret = spi_bus_remove_device(spi_handle_);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Failed to remove SPI device: %s", esp_err_to_name(ret));
    ok = false;
  }
  spi_handle_ = nullptr;

  if (owned_spi_bus_) {
    ret = spi_bus_free(config_.spi_host);
    if (ret != ESP_OK) {
      ESP_LOGE(kTag, "Failed to free SPI bus: %s", esp_err_to_name(ret));
      ok = false;
    }
    owned_spi_bus_ = false;
  }

  ESP_LOGI(kTag, "Deinitialized");
  return ok;
}

// ---------------------------------------------------------------------------
// Display control
// ---------------------------------------------------------------------------

void DisplayEpdW21::Display(uint8_t* image) {
  const uint32_t width  = (kWidth % 8 == 0) ? (kWidth / 8) : (kWidth / 8 + 1);
  const uint32_t length = width * kHeight;

  // Hold the bus exclusive while clocking the framebuffer + update trigger so
  // the IMU reader task cannot break the EPD's manual-CS framing.
  AcquireBus();

  WriteCommand(0x4E);
  WriteData(0x00);
  WriteCommand(0x4F);
  WriteData(0x00);
  WriteData(0x00);

  // Stream the whole framebuffer in one transaction. The SSD1680 keeps CS# low
  // across the command + all RAM bytes (datasheet Fig 6-1), so after the 0x24
  // Write-RAM command we hold CS low, set DC high, and burst all pixels at once.
  // The buffer is expected to already be in panel send-order (orientation is set
  // via the GUI rotate/mirror config), so no per-byte reordering happens here.
  WriteCommand(0x24);
  gpio_set_level(config_.cs_pin, 0);
  gpio_set_level(config_.dc_pin, 1);
  SpiWriteBuffer(image, length);
  gpio_set_level(config_.cs_pin, 1);

  TriggerUpdate();

  // Release before the multi-second panel refresh so the IMU can run again.
  ReleaseBus();
  WaitBusy();
}

void DisplayEpdW21::Update() {
  AcquireBus();
  TriggerUpdate();
  ReleaseBus();
  WaitBusy();
}

void DisplayEpdW21::WhiteScreen() {
  AcquireBus();
  WriteCommand(0x24);
  for (int i = 0; i < kHeight; i++) {
    for (int j = 0; j < kWidth / 8; j++) {
      WriteData(0xFF);
    }
  }
  TriggerUpdate();
  ReleaseBus();
  WaitBusy();
}

void DisplayEpdW21::DeepSleep() {
  AcquireBus();
  WriteCommand(0x10);
  WriteData(0x01);
  ReleaseBus();
  vTaskDelay(pdMS_TO_TICKS(100));
}

void DisplayEpdW21::HwReset() {
  Fxl6408::WritePin(config_.rst_pin, false);
  vTaskDelay(pdMS_TO_TICKS(10));
  Fxl6408::WritePin(config_.rst_pin, true);
  vTaskDelay(pdMS_TO_TICKS(10));
}

void DisplayEpdW21::WaitBusy() {
  bool busy = false;
  while (Fxl6408::ReadPin(config_.busy_pin, &busy) && busy) {
    vTaskDelay(pdMS_TO_TICKS(5));
  }
}

// ---------------------------------------------------------------------------
// LED front light (PWM via LEDC)
// ---------------------------------------------------------------------------

bool DisplayEpdW21::InitFrontLight() {
  ledc_timer_config_t timer_cfg = {};
  timer_cfg.speed_mode      = kFrontLightSpeedMode;
  timer_cfg.duty_resolution = kFrontLightResolution;
  timer_cfg.timer_num       = kFrontLightTimer;
  timer_cfg.freq_hz         = config_.front_light_pwm_hz;
  timer_cfg.clk_cfg         = LEDC_AUTO_CLK;
  esp_err_t ret = ledc_timer_config(&timer_cfg);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Front light LEDC timer config failed: %s", esp_err_to_name(ret));
    return false;
  }

  ledc_channel_config_t ch_cfg = {};
  ch_cfg.gpio_num   = config_.front_light_pin;
  ch_cfg.speed_mode = kFrontLightSpeedMode;
  ch_cfg.channel    = kFrontLightChannel;
  ch_cfg.timer_sel  = kFrontLightTimer;
  ch_cfg.duty       = 0;  // Start dark.
  ch_cfg.hpoint     = 0;
  ret = ledc_channel_config(&ch_cfg);
  if (ret != ESP_OK) {
    ESP_LOGE(kTag, "Front light LEDC channel config failed: %s", esp_err_to_name(ret));
    return false;
  }

  front_light_ready_ = true;
  ESP_LOGI(kTag, "Front light ready (GPIO:%d %dHz)", config_.front_light_pin,
           config_.front_light_pwm_hz);
  return true;
}

void DisplayEpdW21::SetFrontLight(float level) {
  if (!front_light_ready_) {
    ESP_LOGW(kTag, "SetFrontLight before front light init");
    return;
  }
  level = std::clamp(level, 0.0f, 1.0f);
  uint32_t duty = static_cast<uint32_t>(lroundf(level * kFrontLightMaxDuty));

  esp_err_t ret = ledc_set_duty(kFrontLightSpeedMode, kFrontLightChannel, duty);
  if (ret == ESP_OK) {
    ret = ledc_update_duty(kFrontLightSpeedMode, kFrontLightChannel);
  }
  if (ret != ESP_OK) {
    ESP_LOGW(kTag, "SetFrontLight failed: %s", esp_err_to_name(ret));
  }
}

void DisplayEpdW21::WriteCommand(uint8_t cmd) {
  gpio_set_level(config_.cs_pin, 0);
  gpio_set_level(config_.dc_pin, 0);
  SpiWrite(cmd);
  gpio_set_level(config_.cs_pin, 1);
}

void DisplayEpdW21::WriteData(uint8_t data) {
  gpio_set_level(config_.cs_pin, 0);
  gpio_set_level(config_.dc_pin, 1);
  SpiWrite(data);
  gpio_set_level(config_.cs_pin, 1);
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

void DisplayEpdW21::ApplyHwInit() {
  HwReset();
  WaitBusy();

  AcquireBus();
  WriteCommand(0x12);  // SWRESET
  ReleaseBus();
  WaitBusy();

  AcquireBus();
  // Driver Output Control: MUX=263 (264 gate lines), GD=0, SM=0, TB=0.
  WriteCommand(0x01);
  WriteData(0x07);  // MUX[7:0] = 263 & 0xFF
  WriteData(0x01);  // MUX[8]   = 263 >> 8
  WriteData(0x00);  // GD=0, SM=0, TB=0

  // Data Entry Mode: Y-increment, X-increment, address update in X direction.
  WriteCommand(0x11);
  WriteData(0x03);

  // RAM X address window: 0x00 to 0x15 (covers 176 source pins).
  WriteCommand(0x44);
  WriteData(0x00);
  WriteData(0x15);

  // RAM Y address window: 0x0000 to 0x0107 (covers 264 gate lines).
  WriteCommand(0x45);
  WriteData(0x00);
  WriteData(0x00);
  WriteData(0x07);
  WriteData(0x01);

  // RAM address counters to (0, 0).
  WriteCommand(0x4E);
  WriteData(0x00);
  WriteCommand(0x4F);
  WriteData(0x00);
  WriteData(0x00);

  ReleaseBus();
  WaitBusy();
}

void DisplayEpdW21::TriggerUpdate() {
  WriteCommand(0x22);
  WriteData(0xF7);
  WriteCommand(0x20);
}

void DisplayEpdW21::AcquireBus() {
  if (spi_handle_ != nullptr) {
    spi_device_acquire_bus(spi_handle_, portMAX_DELAY);
  }
}

void DisplayEpdW21::ReleaseBus() {
  if (spi_handle_ != nullptr) {
    spi_device_release_bus(spi_handle_);
  }
}

void DisplayEpdW21::SpiWrite(uint8_t value) {
  spi_transaction_t t = {};
  t.length     = 8;
  t.flags      = SPI_TRANS_USE_TXDATA;
  t.tx_data[0] = value;
  spi_device_polling_transmit(spi_handle_, &t);
}

void DisplayEpdW21::SpiWriteBuffer(const uint8_t* data, size_t len) {
  if (len == 0) return;
  spi_transaction_t t = {};
  t.length    = len * 8;  // length is in bits
  t.tx_buffer = data;
  spi_device_polling_transmit(spi_handle_, &t);
}
