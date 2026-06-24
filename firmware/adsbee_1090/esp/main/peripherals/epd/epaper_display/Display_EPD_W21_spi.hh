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

  // Selects which custom partial-refresh LUT DisplayFaster() uploads:
  //   kPlain     — pure differential: only changed pixels are driven (fastest).
  //   kReinforce — also re-drives unchanged pixels each refresh (like the OTP
  //                partial mode) for crisper solids / less ghosting.
  //   kFast5Hz   — like kReinforce but with far fewer drive frames (~5 vs ~14)
  //                to target ~5 Hz refresh. Faster, but weaker drive accumulates
  //                ghosting sooner — pair with a periodic full Display().
  enum class PartialLut { kPlain, kReinforce, kFast5Hz };

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
  //
  // The write methods below are NON-BLOCKING: they stream the framebuffer and
  // trigger the refresh, then return immediately while the panel refreshes
  // (BUSY stays high for the duration). The SSD1680 must not be written while a
  // refresh is running (datasheet 0x20: "do not interrupt ... to avoid
  // corruption"), so callers must gate every write on !IsBusy():
  //
  //     if (!epd.IsBusy()) epd.DisplayFast(fb);   // continuous fast updates
  //
  // For a simple synchronous render (e.g. a boot splash) use DisplayBlocking().
  //
  // Ghosting: fast (differential) refreshes accumulate ghosting; intersperse a
  // periodic full Display() to clear it (see DisplayFast notes).

  // True if the panel is mid-refresh (BUSY asserted). Non-blocking; reads BUSY
  // over the GPIO expander (one I2C transaction). Returns true on read failure
  // (fail-safe: callers must not write into a refresh).
  bool IsBusy();

  // Full-screen refresh (fast waveform). This FLASHES/inverts the whole panel
  // and fully clears ghosting — use it to (re)baseline. Returns immediately
  // (non-blocking). Image is kWidth/8 * kHeight bytes, one bit per pixel, in
  // panel order. Calling this invalidates the partial baseline, so the next
  // DisplayFast() re-stages its base image.
  void Display(uint8_t* image);

  // Like Display() but waits for the refresh to complete before returning.
  // For boot/one-shot use where blocking is acceptable.
  void DisplayBlocking(uint8_t* image);

  // True PARTIAL (differential, Display Mode 2) refresh: no full-screen flash,
  // sub-second, intended for continuous motion. The FIRST call stages `image`
  // as the base reference (blocking: one clean full refresh); subsequent calls
  // are non-blocking differential updates that diff against the previous frame
  // (RAM ping-pong promotes each new frame to the reference). Some ghosting
  // still accumulates over many frames — intersperse a periodic Display() to
  // clear it. Must be called only when !IsBusy() (after the first call).
  void DisplayFast(uint8_t* image);

  // Like DisplayFast() but uses the vendor's custom partial-refresh waveform
  // LUT (~0.3 s) instead of the controller's built-in OTP partial waveform.
  // The waveform + voltage/timing registers are uploaded from RAM (not OTP) and
  // activated with 0x22=0xCC (vs. DisplayFast()'s 0xFC). The FIRST call stages
  // `image` as the base reference and uploads the LUT once (blocking); each
  // subsequent call is a non-blocking differential update. Same contract as
  // DisplayFast(): call only when !IsBusy() (after the first call), and
  // intersperse a periodic Display() to clear accumulated ghosting.
  //
  // DisplayFast() and DisplayFaster() set conflicting waveform/display-option
  // state, so they are mutually exclusive: switching between them re-stages the
  // base on the next call.
  //
  // `lut` picks the waveform (see PartialLut). Switching `lut` between calls
  // re-stages on the next call (the LUT is uploaded once per init).
  void DisplayFaster(uint8_t* image, PartialLut lut = PartialLut::kPlain);

  // Triggers a full display update sequence and waits for completion.
  void Update();

  // Fills the display with white and performs a full update (non-blocking).
  void WhiteScreen();

  // Powers the analog booster + oscillator back down (0x22=0x83) without driving
  // the panel. The Display*/Trigger* updates leave the booster ON between frames
  // (so rapid refreshes skip the soft-start ramp); call this when continuous fast
  // updates stop so the panel isn't left drawing booster current. Lighter than
  // DeepSleep() — the panel stays awake and ready for the next update.
  void PowerDown();

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

  // Writes the full-refresh trigger commands (0x22=0xF4 / 0x20). Bus must be held.
  void TriggerUpdate();

  // Writes the fast-refresh trigger commands (0x22=0xC4 / 0x20). Bus must be held.
  void TriggerFastUpdate();

  // Writes the partial/differential trigger commands (0x22=0xFC / 0x20). Bus held.
  void TriggerPartialUpdate();

  // Writes the custom-LUT partial trigger commands (0x22=0xCC / 0x20): activate
  // using the register-loaded waveform (no temp/OTP reload), leaving the booster
  // on for the next frame. Bus must be held.
  void TriggerFasterUpdate();

  // Sets the RAM address counter to (0,0) and bursts the whole framebuffer into
  // the given RAM bank (0x24 = BW, 0x26 = "old"/red) in one SPI transaction.
  // Bus must be held.
  void WriteRamFull(uint8_t ram_cmd, const uint8_t* image);

  // Loads the fast (differential) waveform once: HW reset, SWRESET, and the
  // temperature-forced LUT load from the vendor EPD_HW_Init_Fast sequence. Sets
  // fast_ready_. Blocking but short (LUT load, not a panel refresh).
  bool InitFast();

  // Prepares the panel for partial (Display Mode 2) refresh: enables RAM
  // ping-pong (0x37 F[6]), locks the border (0x3C=0x80), and stages `base` into
  // both RAM banks with one clean full refresh so the first differential update
  // has a reference. Sets partial_ready_. Blocking (the base full refresh waits).
  bool InitPartial(const uint8_t* base);

  // Prepares the panel for the vendor custom-LUT partial path (DisplayFaster):
  // HW reset, restore gate/entry/window config, upload the custom waveform LUT
  // and voltage/timing registers (0x32/0x3F/0x03/0x04/0x2C/0x37), lock the
  // border (0x3C=0x80), stage `base` into both RAM banks, and do one clean full
  // refresh to show it. `lut` selects which waveform array is uploaded. Sets
  // faster_ready_ and active_partial_lut_. Blocking (the base full refresh waits).
  bool InitFaster(const uint8_t* base, PartialLut lut);

  // Acquire/release the shared SPI bus around the EPD's manual-CS sequences so
  // the IMU reader task cannot interleave its transactions mid-frame.
  void AcquireBus();
  void ReleaseBus();

  const Config config_;

  spi_device_handle_t spi_handle_   = nullptr;
  bool                owned_spi_bus_ = false;
  bool                front_light_ready_ = false;  // LEDC configured.
  bool                fast_ready_        = false;  // Fast (Display Mode 1) waveform LUT loaded.
  bool                partial_ready_     = false;  // Partial mode staged (ping-pong + base).
  bool                faster_ready_      = false;  // Custom-LUT partial staged (LUT + base).
  PartialLut          active_partial_lut_ = PartialLut::kPlain;  // Which LUT InitFaster uploaded.
};
