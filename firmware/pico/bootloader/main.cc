// #include "boot_utils.hh"
#include "firmware_update.hh"
#include "hal.hh"

static const uint16_t kStatusLEDPin = 15;

static const uint16_t kBlinkDurationMs = 100;
static const uint16_t kNumBlinks = 2;

static inline void set_status_led_for_duration(bool led_on, uint16_t duration_ms) {
    gpio_put(kStatusLEDPin, led_on);
    busy_wait_ms(duration_ms);
}

static inline void blink_morse(bool dot) {
    set_status_led_for_duration(true, dot ? 100 : 300);
    set_status_led_for_duration(false, 100);
}

static inline void curl_up_and_die() {
    // Curl up and die.
    uint32_t morse_time_unit_ms = 100;
    while (true) {
        // Flash SOS in morse code.
        blink_morse(true);
        blink_morse(true);
        blink_morse(true);
        blink_morse(false);
        blink_morse(false);
        blink_morse(false);
        blink_morse(true);
        blink_morse(true);
        blink_morse(true);
        busy_wait_ms(7 * morse_time_unit_ms);
    }
}

int main() {
    stdio_init_all();

    gpio_init(kStatusLEDPin);
    gpio_set_dir(kStatusLEDPin, GPIO_OUT);
    printf("ADSBEE 1090 BOOTLOADER\r\n");
    for (uint16_t i = 0; i < kNumBlinks; i++) {
        set_status_led_for_duration(true, kBlinkDurationMs / 2);
        set_status_led_for_duration(false, kBlinkDurationMs / 2);
        // i = 0;  // loop forever
    }

    // Try booting valid partitions first.
    printf("Searching for valid partitions...\r\n");
    for (uint16_t i = 0; i < FirmwareUpdateManager::kNumPartitions; i++) {
        if (FirmwareUpdateManager::flash_partition_headers[i]->status ==
            FirmwareUpdateManager::kFlashPartitionStatusValid) {
            printf("\tBooting partition %u.\r\n", i);
            FirmwareUpdateManager::BootPartition(i);
        }
    }
    // Try booting stale partitions second.
    for (uint16_t i = 0; i < FirmwareUpdateManager::kNumPartitions; i++) {
        if (FirmwareUpdateManager::flash_partition_headers[i]->status ==
            FirmwareUpdateManager::kFlashPartitionStatusStale) {
            printf("\tBooting partition %u.\r\n", i);
            FirmwareUpdateManager::BootPartition(i);
        }
    }

    curl_up_and_die();
}