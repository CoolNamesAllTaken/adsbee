#pragma once

#include <cstdint>
#include <cstring>

/**
 * Decides at boot whether the ESP32 runs the application image embedded in the RP2040 firmware.
 *
 * Versions are compared first. On a match the ESP32's application hash is compared with the embedded image's: the
 * SHA-256 of the application's ELF file, which the ESP-IDF build stores in the image and the running application
 * holds in memory.
 */
class ESP32FirmwareCheck {
   public:
    static constexpr uint16_t kHashLenBytes = 32;

    enum Verdict : uint8_t {
        kUpToDate = 0,
        kNoResponse,       // The ESP32 did not report a version.
        kVersionMismatch,  // The ESP32 runs another version.
        kHashNotReported,  // Same version, no hash: firmware from before the hash was reported, or a failed read.
        kHashMismatch      // Same version, another build.
    };

    /**
     * Reads the application hash from an ESP-IDF application image.
     * @param[in] image Application image, as written to flash.
     * @param[in] image_len_bytes Length of the image.
     * @param[out] hash kHashLenBytes Bytes.
     * @retval False if the image has no application description or its hash is blank.
     */
    static bool GetImageHash(const uint8_t* image, uint32_t image_len_bytes, uint8_t* hash) {
        if (image == nullptr || image_len_bytes < kAppDescriptionOffsetBytes + kAppDescriptionLenBytes) {
            return false;
        }
        if (image[0] != kImageMagic) {
            return false;
        }
        uint32_t app_description_magic;
        memcpy(&app_description_magic, image + kAppDescriptionOffsetBytes, sizeof(app_description_magic));
        if (app_description_magic != kAppDescriptionMagic) {
            return false;
        }
        const uint8_t* image_hash = image + kAppDescriptionOffsetBytes + kAppDescriptionHashOffsetBytes;
        bool blank = true;
        for (uint16_t i = 0; i < kHashLenBytes; i++) {
            if (image_hash[i] != 0) blank = false;
        }
        if (blank) {
            return false;
        }
        memcpy(hash, image_hash, kHashLenBytes);
        return true;
    }

    /**
     * @param[in] version_read True if the ESP32 reported its version.
     * @param[in] esp32_version Version reported by the ESP32.
     * @param[in] version This firmware's version.
     * @param[in] image_hash Hash of the embedded image, or nullptr if it has none: versions alone decide then.
     * @param[in] esp32_hash Hash reported by the ESP32, or nullptr if it reported none.
     */
    static Verdict Evaluate(bool version_read, uint32_t esp32_version, uint32_t version, const uint8_t* image_hash,
                            const uint8_t* esp32_hash) {
        if (!version_read) {
            return kNoResponse;
        }
        if (esp32_version != version) {
            return kVersionMismatch;
        }
        if (image_hash == nullptr) {
            return kUpToDate;
        }
        if (esp32_hash == nullptr) {
            return kHashNotReported;
        }
        return memcmp(image_hash, esp32_hash, kHashLenBytes) == 0 ? kUpToDate : kHashMismatch;
    }

    /**
     * True if the ESP32 can run without an update although the check did not pass: it reported this firmware's version
     * and the update attempt wrote nothing, so its flash is as it was.
     * @param[in] num_images_written Images the update attempt started to write.
     */
    static bool UsableAsIs(Verdict verdict, uint16_t num_images_written) {
        return num_images_written == 0 && (verdict == kHashNotReported || verdict == kHashMismatch);
    }

    static const char* VerdictToString(Verdict verdict) {
        switch (verdict) {
            case kUpToDate:
                return "up to date";
            case kNoResponse:
                return "no response";
            case kVersionMismatch:
                return "version mismatch";
            case kHashNotReported:
                return "no application hash reported";
            case kHashMismatch:
                return "application hash mismatch";
        }
        return "unknown";
    }

   private:
    // ESP-IDF application image layout: esp_image_header_t (24 Bytes), one esp_image_segment_header_t (8 Bytes), then
    // esp_app_desc_t, whose app_elf_sha256 follows 144 Bytes of other fields.
    static constexpr uint8_t kImageMagic = 0xE9;
    static constexpr uint32_t kAppDescriptionMagic = 0xABCD5432;
    static constexpr uint32_t kAppDescriptionOffsetBytes = 32;
    static constexpr uint32_t kAppDescriptionHashOffsetBytes = 144;
    static constexpr uint32_t kAppDescriptionLenBytes = 256;
};
