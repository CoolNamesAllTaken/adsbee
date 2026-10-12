#pragma once

#include <cstddef>
#include <cstdint>
#include <cstring>

// Streaming SHA-256 (FIPS 180-4). Small and portable, so the same code runs on the ESP32 and in host tests.
class SHA256 {
   public:
    static constexpr size_t kDigestLenBytes = 32;

    SHA256() { Reset(); }

    void Reset() {
        static const uint32_t kInit[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                                          0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
        memcpy(h_, kInit, sizeof(h_));
        len_bytes_ = 0;
        buf_len_ = 0;
    }

    void Update(const uint8_t* data, size_t len) {
        len_bytes_ += len;
        while (len > 0) {
            size_t n = sizeof(buf_) - buf_len_;
            if (n > len) n = len;
            memcpy(buf_ + buf_len_, data, n);
            buf_len_ += n;
            data += n;
            len -= n;
            if (buf_len_ == sizeof(buf_)) {
                Block(buf_);
                buf_len_ = 0;
            }
        }
    }

    // Writes the digest as 64 lowercase hex characters plus a NUL. The object must be Reset() before reuse.
    void FinalHex(char hex[2 * kDigestLenBytes + 1]) {
        uint64_t len_bits = len_bytes_ * 8;
        uint8_t pad[72] = {0x80};
        size_t pad_len = (buf_len_ < 56 ? 56 : 120) - buf_len_;
        for (int i = 0; i < 8; i++) pad[pad_len + i] = static_cast<uint8_t>(len_bits >> (56 - 8 * i));
        Update(pad, pad_len + 8);
        static const char kHex[] = "0123456789abcdef";
        for (int i = 0; i < 32; i++) {
            uint8_t b = static_cast<uint8_t>(h_[i / 4] >> (24 - 8 * (i % 4)));
            hex[2 * i] = kHex[b >> 4];
            hex[2 * i + 1] = kHex[b & 0xF];
        }
        hex[64] = '\0';
    }

   private:
    static uint32_t Rotr(uint32_t x, int n) { return (x >> n) | (x << (32 - n)); }

    void Block(const uint8_t* p) {
        static const uint32_t kK[64] = {
            0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
            0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
            0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
            0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
            0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
            0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
            0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
            0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};
        uint32_t w[64];
        for (int i = 0; i < 16; i++) {
            w[i] = (uint32_t)p[4 * i] << 24 | (uint32_t)p[4 * i + 1] << 16 | (uint32_t)p[4 * i + 2] << 8 | p[4 * i + 3];
        }
        for (int i = 16; i < 64; i++) {
            uint32_t s0 = Rotr(w[i - 15], 7) ^ Rotr(w[i - 15], 18) ^ (w[i - 15] >> 3);
            uint32_t s1 = Rotr(w[i - 2], 17) ^ Rotr(w[i - 2], 19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16] + s0 + w[i - 7] + s1;
        }
        uint32_t a = h_[0], b = h_[1], c = h_[2], d = h_[3], e = h_[4], f = h_[5], g = h_[6], h = h_[7];
        for (int i = 0; i < 64; i++) {
            uint32_t t1 = h + (Rotr(e, 6) ^ Rotr(e, 11) ^ Rotr(e, 25)) + ((e & f) ^ (~e & g)) + kK[i] + w[i];
            uint32_t t2 = (Rotr(a, 2) ^ Rotr(a, 13) ^ Rotr(a, 22)) + ((a & b) ^ (a & c) ^ (b & c));
            h = g;
            g = f;
            f = e;
            e = d + t1;
            d = c;
            c = b;
            b = a;
            a = t1 + t2;
        }
        h_[0] += a;
        h_[1] += b;
        h_[2] += c;
        h_[3] += d;
        h_[4] += e;
        h_[5] += f;
        h_[6] += g;
        h_[7] += h;
    }

    uint32_t h_[8];
    uint64_t len_bytes_;
    uint8_t buf_[64];
    size_t buf_len_;
};
