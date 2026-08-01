#include "terrain_codec.hh"

#include <cstdlib>  // abs

#include "esp_log.h"
#include "miniz.h"  // ESP32-S3 ROM tinfl (esp_rom public header); zero flash cost

namespace winglet_terrain {

namespace {
constexpr char kTag[] = "terrain_codec";

// PNG-style filter types (must match mapfmt.py _FILT_* ordering).
enum FilterType : uint8_t {
    kFiltNone = 0,
    kFiltSub = 1,
    kFiltUp = 2,
    kFiltAvg = 3,
    kFiltPaeth = 4,
};
}  // namespace

bool InflateRaw(const uint8_t* src, size_t src_len, uint8_t* out, size_t out_len,
                void* decompressor) {
    // Use the STREAMING tinfl API with a caller-provided (PSRAM) decompressor,
    // NOT tinfl_decompress_mem_to_mem — that one-shot helper stack-allocates the
    // ~11 KB tinfl_decompressor and overflows the main task's stack.
    if (!decompressor) {
        ESP_LOGW(kTag, "inflate: null decompressor");
        return false;
    }
    static_assert(kTinflDecompressorSize >= sizeof(tinfl_decompressor),
                  "kTinflDecompressorSize too small for tinfl_decompressor");
    tinfl_decompressor* r = (tinfl_decompressor*)decompressor;
    tinfl_init(r);

    // Raw DEFLATE (no zlib header/adler): omit TINFL_FLAG_PARSE_ZLIB_HEADER. The
    // output buffer holds the whole result (non-wrapping), and all input is
    // present in one buffer (no HAS_MORE_INPUT).
    size_t in_bytes = src_len;
    size_t out_bytes = out_len;
    tinfl_status status = tinfl_decompress(r, (const mz_uint8*)src, &in_bytes, out,
                                           out, &out_bytes,
                                           TINFL_FLAG_USING_NON_WRAPPING_OUTPUT_BUF);
    if (status != TINFL_STATUS_DONE || out_bytes != out_len) {
        ESP_LOGW(kTag, "inflate failed: status=%d out=%u want=%u", (int)status,
                 (unsigned)out_bytes, (unsigned)out_len);
        return false;
    }
    return true;
}

bool PredictorUnfilter(const uint8_t* filtered, size_t filtered_len, uint8_t* out,
                       int h, int w) {
    if (filtered_len != (size_t)h * (w + 1)) {
        ESP_LOGW(kTag, "predictor size mismatch: %u != %d*%d", (unsigned)filtered_len, h, w + 1);
        return false;
    }
    size_t pos = 0;
    for (int y = 0; y < h; y++) {
        uint8_t ft = filtered[pos++];
        const uint8_t* res = filtered + pos;
        pos += w;
        uint8_t* cur = out + (size_t)y * w;
        const uint8_t* up = (y > 0) ? (out + (size_t)(y - 1) * w) : nullptr;

        switch (ft) {
            case kFiltNone:
                for (int x = 0; x < w; x++) cur[x] = res[x];
                break;
            case kFiltUp:
                if (up) {
                    for (int x = 0; x < w; x++) cur[x] = (uint8_t)(res[x] + up[x]);
                } else {
                    for (int x = 0; x < w; x++) cur[x] = res[x];
                }
                break;
            case kFiltSub:
                for (int x = 0; x < w; x++) {
                    int left = (x > 0) ? cur[x - 1] : 0;
                    cur[x] = (uint8_t)(res[x] + left);
                }
                break;
            case kFiltAvg:
                for (int x = 0; x < w; x++) {
                    int left = (x > 0) ? cur[x - 1] : 0;
                    int u = up ? up[x] : 0;
                    cur[x] = (uint8_t)(res[x] + ((left + u) >> 1));
                }
                break;
            case kFiltPaeth:
                for (int x = 0; x < w; x++) {
                    int a = (x > 0) ? cur[x - 1] : 0;       // left
                    int b = up ? up[x] : 0;                 // up
                    int c = (x > 0 && up) ? up[x - 1] : 0;  // up-left
                    int p = a + b - c;
                    int pa = std::abs(p - a), pb = std::abs(p - b), pc = std::abs(p - c);
                    int pred = (pa <= pb && pa <= pc) ? a : (pb <= pc ? b : c);
                    cur[x] = (uint8_t)(res[x] + pred);
                }
                break;
            default:
                ESP_LOGW(kTag, "unknown predictor filter %u at row %d", ft, y);
                return false;
        }
    }
    return true;
}

bool DecodeBlock(uint8_t codec, uint8_t fill, const uint8_t* stored, size_t stored_len,
                 uint8_t* out, uint16_t raw_len, uint8_t* scratch, void* decompressor) {
    switch (codec) {
        case kCodecConstant:
            for (uint16_t i = 0; i < raw_len; i++) out[i] = fill;
            return true;
        case kCodecDeflate:
            return InflateRaw(stored, stored_len, out, raw_len, decompressor);
        case kCodecPredDeflate: {
            if (!scratch) {
                ESP_LOGW(kTag, "predictor block needs scratch");
                return false;
            }
            // Filtered stream is h*(w+1) bytes: kBlockDim*(kBlockDim+1). raw_len is
            // kBlockDim*kBlockDim, so inflate into `scratch` sized filtered_len.
            const int dim = kBlockDim;
            size_t filtered_len = (size_t)dim * (dim + 1);
            if (!InflateRaw(stored, stored_len, scratch, filtered_len, decompressor)) return false;
            return PredictorUnfilter(scratch, filtered_len, out, dim, dim);
        }
        default:
            ESP_LOGW(kTag, "unknown block codec %u", codec);
            return false;
    }
}

}  // namespace winglet_terrain
