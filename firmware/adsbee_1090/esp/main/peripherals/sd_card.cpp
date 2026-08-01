#include "peripherals/sd_card.hh"

#include "driver/sdmmc_host.h"
#include "esp_log.h"
#include "esp_timer.h"
#include "esp_vfs_fat.h"
#include "peripherals/fxl6408.hh"
#include "sdmmc_cmd.h"

namespace {
constexpr char kTag[] = "sd_card";
}

bool SdCard::Init() {
    // Configure the card-detect line as an input on the FXL6408 expander. The
    // expander (Expander A) must already be Init()ed by the time this runs.
    Fxl6408::PinConfig cd_cfg;
    cd_cfg.direction = Fxl6408::Direction::kInput;
    cd_cfg.pull = Fxl6408::PullMode::kNone;  // external pull-up present
    if (!Fxl6408::ConfigurePin(config_.cd, cd_cfg)) {
        ESP_LOGE(kTag, "Failed to configure card-detect pin");
        return false;
    }
    cd_configured_ = true;

    // Mount now if a card is already inserted; otherwise defer to Update().
    bool present = IsCardPresent();
    last_present_ = present;
    pending_present_ = present;
    if (present) {
        Mount();  // failure is non-fatal; Update() will retry / clear.
    } else {
        ESP_LOGI(kTag, "No card present at init; will mount on insertion.");
    }
    return true;  // init succeeds regardless of card presence
}

bool SdCard::IsCardPresent() {
    if (!cd_configured_) return false;
    bool level = true;
    if (!Fxl6408::ReadPin(config_.cd, &level)) {
        // I2C read failed; assume no card rather than thrash.
        return false;
    }
    return !level;  // active-low: 0 = present
}

void SdCard::Update() {
    // Rate-limit the card-detect poll (an I2C transaction).
    int64_t now = esp_timer_get_time();
    if (now - last_poll_us_ < (int64_t)config_.cd_poll_interval_ms * 1000) return;
    last_poll_us_ = now;

    bool present = IsCardPresent();

    // Light debounce: a new state must be observed on two consecutive polls
    // before it is accepted, so a bouncing card-detect contact doesn't thrash
    // mount/unmount.
    if (present != last_present_) {
        if (present == pending_present_) {
            // Confirmed on a second consecutive poll -> apply the transition.
            last_present_ = present;
            if (present) {
                ESP_LOGI(kTag, "Card inserted; mounting.");
                Mount();
            } else {
                ESP_LOGI(kTag, "Card removed; unmounting.");
                Unmount();
            }
        } else {
            // First observation of the new state; wait for confirmation.
            pending_present_ = present;
        }
    } else {
        pending_present_ = present;
    }
}

bool SdCard::Mount() {
    if (card_ != nullptr) return true;  // already mounted

    sdmmc_host_t host = SDMMC_HOST_DEFAULT();
    host.flags = SDMMC_HOST_FLAG_1BIT;
    host.max_freq_khz = config_.max_freq_khz;  // High Speed (40 MHz) by default

    sdmmc_slot_config_t slot = SDMMC_SLOT_CONFIG_DEFAULT();
    slot.width = 1;
    slot.clk = config_.clk;
    slot.cmd = config_.cmd;
    slot.d0 = config_.d0;
    // Card-detect is on the I2C expander, not a native SDMMC slot pin, so the
    // host driver can't read it; we poll it ourselves in Update().
    slot.cd = SDMMC_SLOT_NO_CD;
    // External pull-ups are present -> do NOT enable internal pull-ups.

    esp_vfs_fat_sdmmc_mount_config_t mount_cfg = {};
    mount_cfg.format_if_mount_failed = false;
    mount_cfg.max_files = config_.max_files;
    mount_cfg.allocation_unit_size = 16 * 1024;

    esp_err_t err =
        esp_vfs_fat_sdmmc_mount(config_.mount_point, &host, &slot, &mount_cfg, &card_);
    if (err != ESP_OK) {
        // e.g. card removed mid-mount, or unformatted. Non-fatal.
        ESP_LOGW(kTag, "Mount failed (%s); card_=nullptr.", esp_err_to_name(err));
        card_ = nullptr;
        return false;
    }
    ESP_LOGI(kTag, "Card mounted at %s.", config_.mount_point);
    // Headline speed number: the clock the host actually negotiated (requesting
    // 40 MHz doesn't guarantee 40 MHz — the host snaps to the nearest divider).
    ESP_LOGI(kTag, "SD clock: %d kHz (1-bit)", card_->real_freq_khz);
    sdmmc_card_print_info(stdout, card_);
    return true;
}

void SdCard::Unmount() {
    if (card_ == nullptr) return;
    esp_vfs_fat_sdcard_unmount(config_.mount_point, card_);
    card_ = nullptr;
    ESP_LOGI(kTag, "Card unmounted.");
}

// ---------------------------------------------------------------------------
// Validation self-test (single removable block).
// ---------------------------------------------------------------------------
#ifdef SD_CARD_SELF_TEST
#include <dirent.h>
#include <cstdio>
#include <cstring>

void RunSdCardSelfTest(SdCard& sd) {
    if (!sd.IsMounted()) {
        ESP_LOGW(kTag, "SD self-test skipped: no card");
        return;
    }

    // 1. Card info.
    sdmmc_card_print_info(stdout, sd.card());

    char path[64];
    snprintf(path, sizeof path, "%s/wtest.txt", sd.mount_point());
    const char* payload = "adsbee-sd-selftest";

    // 2. Write.
    FILE* f = fopen(path, "w");
    if (!f) {
        ESP_LOGE(kTag, "SD self-test FAIL: open for write (%s)", path);
        return;
    }
    fprintf(f, "%s", payload);
    fflush(f);
    fclose(f);

    // 3. Read back and compare.
    f = fopen(path, "r");
    if (!f) {
        ESP_LOGE(kTag, "SD self-test FAIL: open for read (%s)", path);
        return;
    }
    char buf[64] = {0};
    size_t n = fread(buf, 1, sizeof buf - 1, f);
    fclose(f);
    buf[n] = '\0';
    if (strcmp(buf, payload) != 0) {
        ESP_LOGE(kTag, "SD self-test FAIL: readback mismatch ('%s' != '%s')", buf, payload);
        return;
    }

    // 4. List root directory.
    DIR* dir = opendir(sd.mount_point());
    if (dir) {
        ESP_LOGI(kTag, "Root directory listing:");
        struct dirent* ent;
        while ((ent = readdir(dir)) != nullptr) {
            ESP_LOGI(kTag, "  %s", ent->d_name);
        }
        closedir(dir);
    } else {
        ESP_LOGW(kTag, "SD self-test: opendir(%s) failed", sd.mount_point());
    }

    // 5. Card-detect readout.
    ESP_LOGI(kTag, "Card-detect: present=%d", sd.IsCardPresent() ? 1 : 0);

    // Summary line.
    uint64_t mb = ((uint64_t)sd.card()->csd.capacity * sd.card()->csd.sector_size) / (1024 * 1024);
    ESP_LOGI(kTag, "SD OK: %llu MB, RW verified", (unsigned long long)mb);
}
#endif  // SD_CARD_SELF_TEST
