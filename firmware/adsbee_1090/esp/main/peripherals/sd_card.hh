#pragma once

#include "bsp.hh"
#include "driver/sdmmc_types.h"
#include "peripherals/fxl6408_pin_config.hh"

// Bring-up validation switch. While defined, RunSdCardSelfTest() is compiled and
// app_main runs it once at boot to verify the card mounts and reads/writes.
// Remove this one line (and, if desired, the self-test code it guards) once SD
// bring-up is confirmed.
#define SD_CARD_SELF_TEST
#define TERRAIN_SELF_TEST

// microSD card driver (ESP-IDF SDMMC host, 1-bit mode) with hot-plug support.
//
// The card may be absent at boot and inserted/removed while running, so mounting
// is NOT done once in Init(); it is driven by Update(), which polls the
// active-low card-detect line (on the FXL6408 expander) and mounts on insertion /
// unmounts on removal. Guard all filesystem access on IsMounted().
//
// Init() only configures the card-detect pin and (if a card is already present)
// performs the first mount; it always succeeds even with no card. Update() must
// be called periodically from the main loop.
class SdCard {
   public:
    struct Config {
        gpio_num_t cmd  = bsp.sd_cmd_pin;
        gpio_num_t clk  = bsp.sd_clk_pin;
        gpio_num_t d0   = bsp.sd_dat0_pin;
        fxl6408_pin_t cd = bsp.sd_cd_pin;  // active-low (0 = card present)
        const char* mount_point = "/sd";
        int max_files = 4;
        // Poll card-detect at most this often from Update() (ms).
        uint32_t cd_poll_interval_ms = 200;
        // SDMMC clock. High Speed (40 MHz) is the 1-bit SD ceiling; drop to
        // SDMMC_FREQ_DEFAULT (20 MHz) if a card/wiring proves flaky at 40 MHz.
        int max_freq_khz = SDMMC_FREQ_HIGHSPEED;
    };

    // No-argument default constructor — uses all Config defaults.
    SdCard() : SdCard(Config{}) {}

    // Constructs the driver, storing the config. No SD transactions occur here.
    explicit SdCard(const Config& config) : config_(config) {}

    // Configures the card-detect pin as an input and, if a card is already
    // present, mounts it. Returns true even when no card is present (mounting is
    // deferred to Update()). Requires the FXL6408 Expander A to be Init()ed first.
    bool Init();

    // Polls card-detect (rate-limited) and mounts on insertion / unmounts on
    // removal. Call once per main-loop iteration.
    void Update();

    // True when a card is physically present (card-detect reads low).
    bool IsCardPresent();

    // True when the filesystem is mounted and usable.
    bool IsMounted() const { return card_ != nullptr; }

    const char* mount_point() const { return config_.mount_point; }
    sdmmc_card_t* card() const { return card_; }

   private:
    bool Mount();
    void Unmount();

    Config config_;
    sdmmc_card_t* card_ = nullptr;
    bool cd_configured_ = false;
    bool last_present_ = false;      // debounced presence state (edge detection)
    bool pending_present_ = false;   // candidate state awaiting debounce confirmation
    int64_t last_poll_us_ = 0;
};

// End-to-end validation self-test (compiled only when SD_CARD_SELF_TEST is
// defined). Logs card info and performs a write/read/readback/list round-trip.
// Kept as a single removable unit — delete this declaration, its definition in
// sd_card.cc, and the guarded call site in app_main to remove the feature.
#ifdef SD_CARD_SELF_TEST
void RunSdCardSelfTest(SdCard& sd);
#endif
