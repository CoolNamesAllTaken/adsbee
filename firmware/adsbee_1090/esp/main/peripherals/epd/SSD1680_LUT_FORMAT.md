# SSD1680 / SSD1680A Waveform LUT Format

Reference for authoring custom waveform LUTs for the e-paper driver in
[epaper_display/](epaper_display/) (GDEY027T91 panel, SSD1680A controller). It documents the
`kPartialLut` / `kPartialLutReinforce` / `kPartialLutFast5Hz` arrays in
[Display_EPD_W21_spi.cpp](epaper_display/Display_EPD_W21_spi.cpp) and the vendor `LUT_DATA` /
`LUT_DATA1` / `WS6` tables.

All datasheet citations are to `esp/references/SSD1680.pdf` (SSD1680 Rev 0.14, Jun 2019); page
numbers are the printed footer page (e.g. "p.15" = footer "P 15/46"). Where the datasheet and
hardware disagree, the **hardware-confirmed** values are what ship — those are flagged inline.

---

## 1. Big picture

An e-paper pixel is moved by applying a timed sequence of source voltages relative to a common
(VCOM) electrode. The waveform is defined by a **LUT** (153 bytes, command `0x32`) plus a handful
of voltage/option registers. The LUT has two logically separate parts (datasheet §6.6, p.13–14):

1. **VS (Voltage Selection) tables — LUT0..LUT4.** Five waveforms; one is picked **per pixel** by
   the pixel's RAM bits (see §2a). LUT4 is the VCOM waveform. Each LUT specifies, for all 12
   groups × 4 phases, which voltage level to output.
2. **Timing — TP / SR / RP / FR / XON.** Shared by all five LUTs. Defines how many frames each
   phase lasts, how many times sub-groups and groups repeat, the per-group frame rate, and gate
   scan options.

So: the VS table picks the *voltage per phase* for a given pixel; the timing fields pick the
*duration and repetition* for everyone. A pixel's drive = its LUT's voltages × the shared timing.

The LUT can be loaded from on-chip OTP automatically, or written explicitly by the MCU via `0x32`
(our custom-LUT path). See §5 for upload/activation.

---

## 2. The 153-byte LUT (command `0x32`)

Layout from datasheet Fig 6-6 "Waveform Setting mapping" (p.15). The 153 bytes are:

| Section          | Byte range | Size | Contents                                              |
|------------------|------------|------|-------------------------------------------------------|
| VS table LUT0    | 0–11       | 12   | `VS[0..11 X-L0]` — LUT0 across all 12 groups          |
| VS table LUT1    | 12–23      | 12   | `VS[0..11 X-L1]`                                       |
| VS table LUT2    | 24–35      | 12   | `VS[0..11 X-L2]`                                       |
| VS table LUT3    | 36–47      | 12   | `VS[0..11 X-L3]`                                       |
| VS table LUT4    | 48–59      | 12   | `VS[0..11 X-L4]` — VCOM waveform                       |
| Timing Group 0   | 60–66      | 7    | TP[0A],TP[0B],SR[0AB],TP[0C],TP[0D],SR[0CD],RP[0]     |
| Timing Group 1   | 67–73      | 7    | …group 1                                              |
| Timing Groups 2–11 | 74–143   | 70   | …groups 2–11 (10 × 7)                                 |
| FR[0..11]        | 144–149    | 6    | per-group frame rate (two 4-bit codes per byte)       |
| XON[0..11]       | 150–152    | 3    | per-group "all gate on" selection                     |

5 × 12 + 12 × 7 + 6 + 3 = 60 + 84 + 9 = **153**.

**Important:** each 12-byte VS block is **one LUT across all 12 groups** (one byte per group, that
byte holding the 4 phase codes for that group) — *not* "one transition." Byte `k` of LUT `m` is
`VS[kA-Lm] VS[kB-Lm] VS[kC-Lm] VS[kD-Lm]`, i.e. group `k`, phases A/B/C/D.

### 2a. LUT selection — which pixels use which VS table

Datasheet Table 6-5 (p.13), **black/white display**: the LUT index is chosen by the
(R-RAM bit, B/W-RAM bit) pair:

| R-RAM (0x26) | B/W-RAM (0x24) | Image | LUT used        |
|--------------|----------------|-------|-----------------|
| 0            | 0              | Black | **LUT0** (drives black) |
| 0            | 1              | White | **LUT1** (drives white) |
| 1            | 0              | Black | LUT2 = LUT0     |
| 1            | 1              | White | LUT3 = LUT1     |

LUT4 is the VCOM waveform. B/W RAM bit: **1 = white, 0 = black**.

In **Display Mode 2** (differential / partial), the "R RAM" (`0x26`) holds the *old* frame and the
"B/W RAM" (`0x24`) the *new* frame, so the four indices map to old/new pairs:

| LUT | (old, new) | drives | meaning            |
|-----|------------|--------|--------------------|
| LUT0 | (0,0) = (black, black) | black | unchanged black (reinforce) |
| LUT1 | (0,1) = (black, white) | white | changed to white   |
| LUT2 | (1,0) = (white, black) | black | changed to black   |
| LUT3 | (1,1) = (white, white) | white | unchanged white (reinforce) |

> This is why a *differential* LUT (e.g. `kPartialLut`) zeroes LUT0 and LUT3 (the unchanged cases)
> and only drives LUT1/LUT2 (the changed cases). The *reinforcing* LUT additionally drives LUT0
> (toward black) and LUT3 (toward white) so static areas are re-driven each frame. On our panel
> the shipped reinforce bytes are **LUT0=`0x44` (drive black), LUT1=`0x88`, LUT2=`0x44`,
> LUT3=`0x88` (drive white)** — i.e. on this panel `0x44` ends black and `0x88` ends white (§2b).

### 2b. VS byte encoding (voltage per phase)

Each VS byte covers one group's 4 phases (A,B,C,D), 2 bits per phase, **MSB first** (phase A =
bits 7–6, B = 5–4, C = 3–2, D = 1–0). Datasheet Table 6-6 (p.14):

| 2-bit code | Source voltage | VCOM voltage (LUT4) |
|------------|----------------|---------------------|
| `00`       | VSS            | DCVCOM              |
| `01`       | VSH1           | VSH1 + DCVCOM       |
| `10`       | VSL            | VSL + DCVCOM        |
| `11`       | VSH2           | N/A                 |

The datasheet does **not** bind VSH1/VSL to "black"/"white" — the optical direction depends on the
VCOM sign and the panel. So the black/white direction must be confirmed on hardware.

> **Hardware-confirmed for this panel:** `0x44` (=`01 00 01 00`, VSH1 in phases A & C) drives
> **toward black**; `0x88` (=`10 00 10 00`, VSL in phases A & C) drives **toward white**. Derived
> from the shipped, hardware-correct reinforce bytes plus the §2a datasheet roles: LUT0 (unchanged
> black) = `0x44` and LUT2 (→ black) = `0x44`, so `0x44` → black; LUT1 (→ white) = `0x88` and LUT3
> (unchanged white) = `0x88`, so `0x88` → white. Building the reinforce variant with LUT0/LUT3
> swapped (LUT0=`0x88`, LUT3=`0x44`) inverted the whole panel, confirming this polarity.

A VS byte of `0x00` = no drive in any phase (pixel held). Worked examples:
- `0x88` = `10 00 10 00` → VSL in phase A and C.
- `0x44` = `01 00 01 00` → VSH1 in phase A and C.
- `0x00` = no drive.

The voltage *magnitudes* (VSH1/VSH2/VSL/VGH/VCOM) are set by separate registers — see §3.

### 2c. Timing groups (TP / SR / RP)

Twelve 7-byte groups. Per datasheet Fig 6-6 (p.15) the byte order within group *n* (group 0 at
addr 60) is:

| Offset in group | Field    | Meaning (datasheet p.14)                                  |
|-----------------|----------|----------------------------------------------------------|
| 0               | TP[nA]   | phase A length in frames (0–255; **0 = phase skipped**)   |
| 1               | TP[nB]   | phase B length                                           |
| 2               | SR[nAB]  | state-repeat count for the A&B sub-group                 |
| 3               | TP[nC]   | phase C length                                           |
| 4               | TP[nD]   | phase D length                                           |
| 5               | SR[nCD]  | state-repeat count for the C&D sub-group                 |
| 6               | RP[n]    | repeat count for the whole group                         |

> Note the order: `SR[AB]` is at **offset 2** (between TP[B] and TP[C]), and `SR[CD]` at offset 5.
> A common mistake is to read all four TP bytes first — they are *not* contiguous.

Repeat semantics (p.14): the stored value `v` means **`v + 1` executions** (0 → 1×, 1 → 2×, … max
256). `RP[n]` repeats the whole group; `SR[nAB]`/`SR[nCD]` repeat the A&B / C&D phase pair within
the group. `TP = 0` skips that phase entirely.

Frames contributed by group *n* =
`( (TP[A]+TP[B])·(SR[AB]+1) + (TP[C]+TP[D])·(SR[CD]+1) ) · (RP+1)`.

In our partial LUTs only Group0 is active, with TP[A] the main drive and a single TP[C]=1 settle
frame (offset 63). (Earlier revisions of this doc mislabeled offset 63 as `TP[D]`; per Fig 6-6 it
is `TP[C]`.)

### 2d. FR (frame rate) and XON (gate scan)

- **FR[0..11]** (bytes 144–149): per-group frame frequency, **range 0–7** (datasheet p.14), packed
  two 4-bit codes per byte (FR[0] high nibble of byte 144, FR[1] low nibble, …). The on-chip
  oscillator is adjustable **25–200 Hz** (p.4). The datasheet gives **no** code→Hz table, so the
  absolute ms-per-frame must be calibrated empirically. Our anchor: the vendor `LUT_DATA` is
  labeled 1.52 s and decodes to **56 frames** → **~27 ms/frame** at its FR codes.
- **XON[0..11]** (bytes 150–152): "All Gate On" selection per nAB / nCD sub-group (p.14).
  `XON=0` = normal gate scan in those phases; `XON=1` = all gates held high. Left at `0x00` in our
  LUTs (normal scan).

### 2e. Refresh-time model and tuning

Total BUSY-high time per refresh ≈

```
fixed overhead (booster soft-start + analog ramp, see §7)
  +  Σ over groups [ frames(group) ]  ×  per-frame period(FR)
```

where `frames(group)` is the formula in §2c. The predictable, linear lever is the **frame count**
(TP, expanded by SR/RP). Calibrated at ~27 ms/frame on this panel, plus ~90 ms fixed soft-start
overhead by default (§7).

| LUT variant            | Group0 TP[A] | Group1 TP[A] | ≈ drive frames | ≈ waveform time |
|------------------------|--------------|--------------|----------------|-----------------|
| `kPartialLut` / `…Reinforce` | `0x0c` (12) + TP[C]=1 | `0x01` (1) | ~14 | ~380 ms |
| `kPartialLutFast5Hz`   | `0x04` (4) + TP[C]=1  | `0x00` (0) | ~5  | ~135 ms |

Add the ~90 ms soft-start (§7) to get the measured BUSY time (e.g. ~135 + ~90 ≈ measured ~336 ms
for Fast5Hz before the soft-start/booster optimizations). FR reduction is a second lever but the
absolute effect is unverified; prefer the frame-count lever, and see §7 for cutting the fixed
overhead.

---

## 3. Voltage / level registers (separate commands)

The vendor packs 6 extra bytes after the 153-byte LUT into a 159-byte array for convenience, but
they are **not** part of `0x32` — each goes to its own command (datasheet §6.7, p.15):

| Array idx | WS6 val | Command | Register | POR | Notes |
|-----------|---------|---------|----------|-----|-------|
| 153 | `0x06` | `0x3F` | EOPT (LUT end option) | `0x02` | see §4 |
| 154 | `0x17` | `0x03` | VGH (gate drive)      | `0x00` | see below |
| 155 | `0x41` | `0x04` A | VSH1 (source high 1) | `0x41` | =15 V |
| 156 | `0xa8` | `0x04` B | VSH2 (source high 2) | `0xA8` | =5 V |
| 157 | `0x32` | `0x04` C | VSL (source low)     | `0x32` | =−15 V |
| 158 | `0x00` | `0x2C` | VCOM                  | `0x00` | |

**VGH — `0x03` Gate Driving Voltage Control (p.20):** A[4:0] selects VGH 10–20 V. Selected rows:
`0x00`=20 V (POR), `0x03`=10 V, `0x0B`=14 V, `0x11`=17 V, `0x17`=20 V. Our `0x17` = 20 V.

**Source — `0x04` Source Driving Voltage Control (p.21):** three bytes A=VSH1, B=VSH2, C=VSL,
with **VSH1 ≥ VSH2** required. VSH1/VSH2 have two ranges by bit7 (bit7=1 → 2.4–8.8 V table;
bit7=0 → 9–17 V table); e.g. `0x41`=15 V, `0xA8`=5 V. VSL (C) covers −5…−17 V; `0x32`=−15 V.
Defaults (POR) are exactly our values (15 V / 5 V / −15 V).

**VCOM — `0x2C` Write VCOM register (p.28):** A[7:0], POR `0x00`. Table runs `0x08`=−0.2 V …
`0x64`=−2.5 V … `0x78`=−3 V. Our `0x00` leaves VCOM at the register default.

---

## 4. Border, EOPT, display-option, update-control registers

**`0x3C` Border Waveform Control (p.31):** POR `0xC0` (VBD = HiZ). A[7:6] VBD source: `00`=GS
transition (follow LUT), `01`=fixed level (A[5:4]: `00`VSS/`01`VSH1/`10`VSL/`11`VSH2), `10`=VCOM,
`11`=HiZ. A[1:0] GS transition LUT select: **`00`→LUT0, `01`→LUT1, `10`→LUT2, `11`→LUT3** (this
table independently confirms the LUT indexing in §2a). We write `0x80` to keep the border quiet
during partial updates.

**`0x3F` End Option / EOPT (p.31):** POR `0x02`. `0x22`=Normal; `0x07`=keep previous source output
level before power-off. Our LUTs use `0x06` (WS6[153]) — note this differs from the datasheet's
"Normal" (`0x22`); it is a vendor-chosen value carried verbatim.

**`0x37` Write Register for Display Option (p.30):** 10 bytes A–J. A[7]=spare VCOM OTP select;
B–F = Display Mode bits for the waveform-setting words (`0`=Display Mode 1, `1`=Display Mode 2);
**F[6] = RAM Ping-Pong enable for Display Mode 2** (POR 0); G–J = module ID / waveform version.
Ping-pong is **not supported in Display Mode 1**. (We set F to enable ping-pong — see §6.)

**`0x21` Display Update Control 1 (p.25):** A[7:4] Red-RAM and A[3:0] B/W-RAM content option:
`0000`=Normal, `0100`=bypass (treat as 0), `1000`=inverse. B[7]=source output mode (0: S0–S175,
1: S8–S167). Relevant if a custom LUT wants to bypass the unused red RAM for a pure-B/W single-RAM
setup.

---

## 5. Upload / activation sequence

Loading a custom register LUT and activating it (see `InitFaster` / `TriggerFasterUpdate` in
[Display_EPD_W21_spi.cpp](epaper_display/Display_EPD_W21_spi.cpp)):

```
0x32  ← 153 LUT bytes          (VS tables + timing groups + FR + XON)
0x3F  ← EOPT
0x03  ← VGH
0x04  ← VSH1, VSH2, VSL
0x2C  ← VCOM
0x37  ← 10-byte display option (F[6]=1 → RAM ping-pong; see §6)
0x3C  ← 0x80                   (border quiet during partial)
0x0C  ← optional soft-start    (see §7; if omitted, POR ~90 ms is used)
0x22  ← <update mode>          (Display Update Control 2)
0x20                           (Master Activation — drives the panel; BUSY high)
```

### `0x22` Display Update Control 2 — stage bitfield

Per datasheet p.26, the `0x22` byte is a **bitfield of stages** run on the next `0x20`:

| Bit | 7 | 6 | 5 | 4 | 3 | 2 | 1 | 0 |
|-----|---|---|---|---|---|---|---|---|
| Stage | enable clock | enable analog | load temp | load LUT (OTP) | Display Mode 1 | Display Mode 2 | disable analog | disable OSC |

Documented values (p.26): `0x80` enable clk, `0x01` disable clk, `0xC0` enable analog, `0x03`
disable analog, `0x91`/`0x99` load LUT mode 1/2, `0xB1`/`0xB9` load temp+LUT mode 1/2, `0xC7`
display mode 1, `0xCF` display mode 2, `0xF7` (temp+LUT mode1+display), `0xFF` (temp+LUT
mode2+display). All of `0xC7/0xCF/0xF7/0xFF` end by disabling analog + OSC (bits 1,0).

Notes for custom LUTs:
- **bit4 (load LUT from OTP)** is set in `0xF7`/`0xFF`/`0x91`/`0x99`/`0xB1`/`0xB9`. Running any of
  these **overwrites the LUT register written by `0x32`**. So a one-time OTP baseline (e.g. `0xF7`)
  must come **before** the custom `0x32` upload; afterwards only use a no-OTP-load display value
  (`0xCF`/`0xCC`). This is the bug-and-fix in `InitFaster`.
- **`0xFC`** is a **vendor** value (not in the datasheet's documented list) used by the OTP
  differential path (`DisplayFast`). Bit-wise it does not disable analog/OSC.
- **Leaving the booster on between frames:** clearing bits 1+0 (`& ~0x03`) keeps analog + OSC
  powered after the update, so the next rapid refresh skips the ~90 ms soft-start ramp. The driver
  uses `0xCC` (=`0xCF & ~0x03`), `0xF4` (=`0xF7 & ~0x03`), `0xC4` (=`0xC7 & ~0x03`); `0xFC` already
  has those bits clear. `PowerDown()` (`0x22=0x83`) turns analog+OSC back off when updates stop.

---

## 6. RAM ping-pong (`0x37` byte F bit 6)

With ping-pong enabled (Display Mode 2 only, datasheet p.30), each differential update
auto-promotes the new frame (RAM `0x24`) into the old/reference bank (RAM `0x26`) after the
refresh. So successive partial updates diff against the *previous* frame, not the original
baseline — required for continuous animation when the LUT is uploaded once and RAM isn't manually
re-staged each frame. (Ping-pong is unavailable in Display Mode 1.)

---

## 7. Fixed overhead: booster soft-start (`0x0C`) and drive flow

Each `0x20` activation runs the booster **soft-start** before driving. `0x0C` Booster Soft Start
Control (datasheet p.22): bytes A/B/C = Phase 1/2/3 strength + min-off-time, byte D = duration
where D[1:0]=Phase1, D[3:2]=Phase2, D[5:4]=Phase3, each `00`=10 ms / `01`=20 / `10`=30 / `11`=40.
**POR D = `0x0F`** = Phase1 40 ms + Phase2 40 ms + Phase3 10 ms ≈ **~90 ms fixed per refresh**.

Neither our driver nor the vendor sets `0x0C`, so the slow POR default is used. Setting `0x0C`
with a shorter duration (e.g. D=`0x00` → 10+10+10 ms) cuts this overhead; combine with the
"leave booster on between frames" trick (§5) for back-to-back updates. (Strengths A/B/C POR =
`0x8B/0x9C/0x96`.)

Datasheet general drive flow (§9.1, p.39): … set gate output (`0x01`) → load waveform LUT →
**set softstart (`0x0C`)** → drive (`0x22`,`0x20`) → wait BUSY low.

---

## 8. Quick reference — our three partial LUTs

All are 159-byte arrays (153 LUT + 6 register bytes), selected via `PartialLut`.

**VS tables** (`kPartialLut` = differential; `…Reinforce` and `…Fast5Hz` share reinforcing VS):

| LUT | (old,new) → drives | `kPartialLut` | `…Reinforce` / `…Fast5Hz` |
|-----|--------------------|---------------|----------------------------|
| LUT0 | (black,black) → black | `0x00…` | `0x44…` (drive black) |
| LUT1 | (black,white) → white | `0x88…` | `0x88…`                |
| LUT2 | (white,black) → black | `0x44…` | `0x44…`                |
| LUT3 | (white,white) → white | `0x00…` | `0x88…` (drive white) |
| LUT4 | VCOM                  | `0x00…` | `0x00…`                |

(Hardware-confirmed polarity on this panel: `0x44` ends black, `0x88` ends white — §2b.)

**Timing** differs only between standard and fast (see §2e); FR/XON and the 6 voltage bytes are
identical across all three. Byte order per §2c (`TP[A],TP[B],SR[AB],TP[C],TP[D],SR[CD],RP`):
```
kPartialLut / …Reinforce:  Group0 = 0x0c,00,00,01,00,00,00  (TP[A]=12, TP[C]=1)
                           Group1 = 0x01,00,00,00,00,00,00  (TP[A]=1)   -> ~14 frames
kPartialLutFast5Hz:        Group0 = 0x04,00,00,01,00,00,00  (TP[A]=4,  TP[C]=1)
                           Group1 = 0x00,00,00,00,00,00,00  (dropped)   -> ~5 frames
FR (all):    144..149 = 0x26,0x22,0x22,0x22,0x22,0x22   (FR[n] codes; see §2d)
XON (all):   150..152 = 0x00,0x00,0x00
Voltages (all): EOPT=0x06 VGH=0x17(20V) VSH1=0x41(15V) VSH2=0xa8(5V) VSL=0x32(-15V) VCOM=0x00
```
