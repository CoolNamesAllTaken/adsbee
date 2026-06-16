#pragma once

#include <cstdint>
#include "driver/gpio.h"
#include "driver/ledc.h"
#include "driver/spi_master.h"
#include "bsp.hh"
#include "peripherals/fxl6408.hh"

// SSD1680A E-Paper Display Driver
// Datasheet: https://www.waveshare.com/w/upload/7/7f/SSD1680_1.pdf
//
// RST and BUSY are routed through a GPIO expander on this board; provide
// implementations via the Config callbacks. CS and DC are direct GPIO.

class DisplayEpdW21 {
 public:
  static constexpr int kWidth  = 176;
  static constexpr int kHeight = 264;

  // -------------------------------------------------------------------------
  // Configuration — passed to the constructor.
  // -------------------------------------------------------------------------
  struct Config {
    // SPI host the display lives on.
    spi_host_device_t spi_host = bsp.periph_spi_handle;

    // Pin configuration used when Init(true) initialises the bus.
    gpio_num_t mosi_pin        = bsp.periph_spi_mosi_pin;
    gpio_num_t miso_pin        = bsp.periph_spi_miso_pin;
    gpio_num_t clk_pin         = bsp.periph_spi_clk_pin;
    int        max_transfer_sz = bsp.periph_spi_max_transfer_sz;

    // CS and DC are driven directly on these GPIO pins.
    gpio_num_t cs_pin = GPIO_NUM_12;
    gpio_num_t dc_pin = GPIO_NUM_6;

    // SPI clock frequency (Hz). SSD1680 max write speed is 20 MHz (datasheet
    // Table 12-1); read mode (unused here) is limited to 2.5 MHz. If the panel
    // shows corruption at 20 MHz over the FPC/ZIF cable or GPIO-matrix-routed
    // SPI3 pins, fall back to 10 MHz (the IMU's proven rate on this bus).
    int spi_clock_hz = 20 * 1000 * 1000;

    // RST and BUSY are routed through the GPIO expander.
    fxl6408_pin_t rst_pin  = bsp.epd_rst_pin;
    fxl6408_pin_t busy_pin = bsp.epd_busy_pin;

    // LED front light: PWM (LEDC) on this pin; duty cycle sets brightness.
    // The LEDC timer/channel reserved for it come from the BSP (see the private
    // aliases below); the PWM frequency is front-light-specific.
    gpio_num_t front_light_pin    = bsp.epd_front_light_pin;
    // AP3019A maximum CTRL frequency is 2kHz, but using exactly 2kHz causes
    // the chip to fail to boost the output. 1kHz seems to work fine though.
    int        front_light_pwm_hz = 1000;  
  };

  DisplayEpdW21() : DisplayEpdW21(Config{}) {}
  explicit DisplayEpdW21(const Config& config);
  ~DisplayEpdW21();

  DisplayEpdW21(const DisplayEpdW21&)            = delete;
  DisplayEpdW21& operator=(const DisplayEpdW21&) = delete;

  // -------------------------------------------------------------------------
  // Lifecycle
  // -------------------------------------------------------------------------

  // Initialises GPIO, adds the device to the SPI bus, and configures the
  // panel via the hardware init sequence. Pass init_spi_bus=true for the
  // first device on the bus; subsequent devices sharing the same host should
  // pass false (the default).
  bool Init(bool init_spi_bus = false);

  // Removes the device from the SPI bus. If Init(true) was called, the bus
  // is also freed.
  bool Deinit();

  bool IsInitialized() const { return spi_handle_ != nullptr; }

  // -------------------------------------------------------------------------
  // Display control (call only after Init())
  // -------------------------------------------------------------------------

  // Writes an image framebuffer to the display and triggers a full update.
  // Image must be kWidth/8 * kHeight bytes, one bit per pixel.
  void Display(uint8_t* image);

  // Triggers a full display update sequence and waits for completion.
  void Update();

  // Fills the display with white and performs a full update.
  void WhiteScreen();

  // Issues a deep-sleep command. Call Init() to wake the panel.
  void DeepSleep();

  // Performs a hardware reset sequence via the RST callback.
  void HwReset();

  // Blocks until the BUSY pin goes low (panel ready).
  void WaitBusy();

  // -------------------------------------------------------------------------
  // LED front light (call only after Init())
  // -------------------------------------------------------------------------

  // Sets the front-light brightness. level is clamped to [0.0, 1.0], where
  // 0.0 is off and 1.0 is full brightness (PWM duty cycle = level).
  void SetFrontLight(float level);

  // -------------------------------------------------------------------------
  // Low-level write primitives
  // -------------------------------------------------------------------------
  void WriteCommand(uint8_t cmd);
  void WriteData(uint8_t data);

 private:
  // LEDC timer/channel are reserved by the BSP (see bsp.hh) so all LEDC
  // allocations are visible in one place. Mode and resolution are
  // front-light-specific. ESP32-S3 has only the low-speed mode; 10-bit = 1024
  // brightness steps.
  static constexpr ledc_timer_t     kFrontLightTimer      = bsp.epd_front_light_ledc_timer;
  static constexpr ledc_channel_t   kFrontLightChannel    = bsp.epd_front_light_ledc_channel;
  static constexpr ledc_mode_t      kFrontLightSpeedMode  = LEDC_LOW_SPEED_MODE;
  static constexpr ledc_timer_bit_t kFrontLightResolution = LEDC_TIMER_10_BIT;
  static constexpr uint32_t kFrontLightMaxDuty = (1u << kFrontLightResolution) - 1u;

  void ApplyHwInit();
  void SpiWrite(uint8_t value);

  // Writes a contiguous data buffer in a single SPI transaction (DC must already
  // be high). Used to stream the whole framebuffer at once.
  void SpiWriteBuffer(const uint8_t* data, size_t len);

  // Configures the LEDC timer/channel for the front light and starts it at 0%.
  // Non-fatal: logs and returns false on failure so display Init can continue.
  bool InitFrontLight();

  // Writes the refresh-trigger commands (0x22/0x20). Must be called with the SPI
  // bus already acquired; the caller waits on BUSY *after* releasing the bus so
  // the IMU is not starved during the multi-second panel refresh.
  void TriggerUpdate();

  // Acquire/release the shared SPI bus around the EPD's manual-CS sequences so
  // the IMU reader task cannot interleave its transactions mid-frame.
  void AcquireBus();
  void ReleaseBus();

  const Config config_;

  spi_device_handle_t spi_handle_   = nullptr;
  bool                owned_spi_bus_ = false;
  bool                front_light_ready_ = false;  // LEDC configured.
};
