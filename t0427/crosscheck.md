# ASTERIX cross-check (branch t0427)

**Method.** A recorded 1090 MHz sky capture (RAW `#MDS` log from a bench ADSBee 1090U, 49 minutes, about 120,000
Mode S frames) was replayed on the host through the firmware's own aircraft dictionary and ASTERIX encoder, once
per second as `CommsManager::ReportASTERIX` does. For every CAT021 record the harness also wrote the aircraft state
it was built from, read straight from the dictionary. The ASTERIX stream was then decoded by two independent
decoders, and each decoded field was compared with the value derived from that state and the spec units:

- [asterix_decoder](https://pypi.org/project/asterix_decoder/) 0.7.11 (CroatiaControl, CAT021 Edition 2.6, CAT023 Edition 1.3)
- [libasterix](https://pypi.org/project/libasterix/) 0.36.3 (pure Python, generated from asterix-specs, CAT021 Edition **2.7**, CAT023 1.3, strict parsing)

Both decoders parsed all 35,404 records (8,889 CAT023, 26,515 CAT021) with no errors. Tolerances are half an LSB
of each item. Positions are shown as decode error only.

Records: 26515

| Field | Records with the item | asterix_decoder agrees | libasterix agrees | Largest difference |
|---|---:|---:|---:|---|
| address | 26515 | 26515 | 26515 |  |
| amplitude_dbm | 26515 | 26515 | 26515 |  |
| arc | 26515 | 26515 | 26515 |  |
| atp | 26515 | 26515 | 26515 |  |
| baro_vr_fpm | 24609 | 24609 | 24609 | 3 ft/min |
| callsign | 24546 | 24546 | 24546 |  |
| ecat | 26515 | 26515 | 26515 |  |
| flight_level | 26515 | 26515 | 26515 | 0 FL |
| gbs | 26515 | 26515 | 26515 |  |
| geo_vr_fpm | 1776 | 1776 | 1776 | 3 ft/min |
| geometric_height_ft | 26306 | 26306 | 26306 | 0 ft |
| ground_speed_kts | 26385 | 26385 | 26385 | 0.1094 kt |
| gva | 26515 | 26515 | 26515 |  |
| lat | 26515 | 26515 | 26515 | 1.32e-07 deg |
| lon | 26515 | 26515 | 26515 | 1.32e-07 deg |
| ltt | 26515 | 26515 | 26515 |  |
| mode_3a | 9597 | 9597 | 9597 |  |
| mops_version | 26515 | 26515 | 26515 |  |
| nacp | 26515 | 26515 | 26515 |  |
| nacv | 26515 | 26515 | 26515 |  |
| nic | 26515 | 26515 | 26515 |  |
| nic_baro | 26515 | 26515 | 26515 |  |
| pic | 26515 | 26515 | 26515 |  |
| sac | 26515 | 26515 | 26515 |  |
| sda | 26515 | 26515 | 26515 |  |
| sic | 26515 | 26515 | 26515 |  |
| sil | 26515 | 26515 | 26515 |  |
| sils | 26515 | 26515 | 26515 |  |
| tod_position | 26515 | 26515 | 26515 | 0.005437 s |
| tod_report | 26515 | 26515 | 26515 | 0 s |
| tod_velocity | 26385 | 26385 | 26385 | 0.005437 s |
| track_deg | 26385 | 26385 | 26385 | 0.002747 deg |
| track_number | 26515 | 26515 | 26515 |  |

Sample round: dictionary state / asterix_decoder / libasterix

| ICAO | Callsign | Squawk | FL | Geometric height (ft) | Ground speed (kt) | Track (deg) | Baro rate (ft/min) | NIC / NACp | Position error (m) |
|---|---|---|---|---|---|---|---|---|---|
| AD8BED | JBU1633 / JBU1633 / JBU1633 | - / - / - | 79.25 / 79.25 / 79.25 | 7700 / 7700 / 7700 | 254.0 / 254.0 / 254.0 | 253.56 / 253.56 / 253.56 | -1024 / -1025 / -1025 | 8/10 / 8/10 / 8/10 | 0.00 / 0.00 |
| A4BD24 | SKW3356 / SKW3356 / SKW3356 | 3310 / 3310 / 3310 | 213 / 213 / 213 | 21675 / 21675 / 21675 | 398.0 / 397.9 / 397.9 | 129.09 / 129.09 / 129.09 | 1472 / 1475 / 1475 | 8/10 / 8/10 / 8/10 | 0.01 / 0.01 |
| A21F57 | FFT1192 / FFT1192 / FFT1192 | - / - / - | 277 / 277 / 277 | 28325 / 28325 / 28325 | 452.0 / 452.0 / 452.0 | 129.53 / 129.53 / 129.53 | 1088 / 1087.5 / 1087.5 | 8/10 / 8/10 / 8/10 | 0.01 / 0.01 |
| A69F49 | ASA736 / ASA736 / ASA736 | - / - / - | 89.75 / 89.75 / 89.75 | 8800 / 8800 / 8800 | 279.0 / 279.1 / 279.1 | 342.02 / 342.02 / 342.02 | -1472 / -1475 / -1475 | 8/10 / 8/10 / 8/10 | 0.01 / 0.01 |
| A4DD35 | SKW3115 / SKW3115 / SKW3115 | 3267 / 3267 / 3267 | 310 / 310 / 310 | 31875 / 31875 / 31875 | 461.0 / 461.0 / 461.0 | 147.03 / 147.04 / 147.04 | 64 / 62.5 / 62.5 | 8/10 / 8/10 / 8/10 | 0.01 / 0.01 |
| A02D0C | AMX664 / AMX664 / AMX664 | - / - / - | 61.25 / 61.25 / 61.25 | 5875 / 5875 / 5875 | 268.0 / 268.1 / 268.1 | 344.00 / 344.00 / 344.00 | -1344 / -1343.75 / -1343.75 | 8/10 / 8/10 / 8/10 | 0.01 / 0.01 |

No field was present in a decoded record without the aircraft having that value (no spurious items).

## Synthetic cases

Items the capture doesn't contain (UAT targets, airspeed, magnetic heading, emergency status, NOGO without UTC,
surface, beacon and anonymous addresses) were checked with synthetic aircraft on reserved addresses ADF001-ADF005:
[decoded by asterix_decoder](synthetic_decode_asterix_decoder.txt).
