# Contact modes: ASTERIX cross-check (branch t0495)

**Method.** Recorded sky captures from bench ADSBee 1090U units (9 RAW logs, 9,215 one-second rounds, 665,589
Mode S and UAT frames) were replayed on the host through the firmware's
aircraft dictionary and ASTERIX encoder, as `CommsManager::ReportASTERIX` does once per second. Each CAT021 record's
dictionary state and contact type was written alongside. Two independent decoders then decoded the stream:
[asterix_decoder](https://pypi.org/project/asterix_decoder/) 0.7.11 (CAT021 2.6, CAT023 1.3) and
[libasterix](https://pypi.org/project/libasterix/) 0.36.3 (CAT021 2.7, strict). The expected ATP, service ID, link
technology and ADS-B version presence come from each record's contact type and the CAT021 rules, not from the
encoder.

Both decoders parsed all 207,544 records (161,469 CAT021, 46,075 CAT023) with no errors.

## By contact type

| Contact type | Aircraft | CAT021 records | ATP (I021/040) | Service ID (I021/015) | Records with I021/210 | Both decoders agree |
|---|---:|---:|---|---|---:|---:|
| adsb_icao | 393 | 123882 | 0 | 1 | 123882 | 123882 |
| adsr_icao | 17 | 7580 | 0 | 3 | 7580 | 7580 |
| adsr_other | 1 | 349 | 3 | 3 | 349 | 349 |
| tisb_icao | 2 | 276 | 0 | 3 | 0 | 276 |
| tisb_other | 5 | 432 | 3 | 3 | 0 | 432 |
| uat_adsb_icao | 7 | 1744 | 0 | 2 | 1465 | 1744 |
| uat_adsb_other | 1 | 212 | 3 | 2 | 198 | 212 |
| uat_tisb_icao | 171 | 25707 | 0 | 4 | 25707 | 25707 |
| uat_tisb_trackfile | 14 | 1287 | 3 | 4 | 1287 | 1287 |

Every CAT023 round carried the four service status reports (SID/STYP): 1/2 1090 ES, 2/3 UAT, 3/5 1090 TIS-B and
ADS-R, 4/6 UAT TIS-B and ADS-R, in both decoders.

The capture has no DF18 CF=0/1 or 1090 TIS-B track files. A synthetic log of CRC-valid frames on reserved addresses
ADF010-ADF013 (CF=0, CF=1, CF=2 with the ICAO/Mode A flag set, CF=2) gave adsb_icao_nt, adsb_other,
tisb_trackfile and tisb_icao targets (39 records each); all address, ATP, service ID and version fields agree in both
decoders.

## Every field

| Field | Records with the item | asterix_decoder agrees | libasterix agrees | Largest difference |
|---|---:|---:|---:|---|
| address | 161469 | 161469 | 161469 |  |
| amplitude_dbm | 161469 | 161469 | 161469 |  |
| arc | 161469 | 161469 | 161469 |  |
| atp | 161469 | 161469 | 161469 |  |
| baro_vr_fpm | 129545 | 129545 | 129545 | 3.0 / 3.0 |
| callsign | 147833 | 147833 | 147833 |  |
| ecat | 161469 | 161469 | 161469 |  |
| flight_level | 161349 | 161349 | 161349 | 0.0 / 0.0 |
| gbs | 161469 | 161469 | 161469 |  |
| geo_vr_fpm | 30942 | 30942 | 30942 | 3.0 / 3.0 |
| geometric_height_ft | 158348 | 158348 | 158348 | 0.0 / 0.0 |
| ground_speed_kts | 159689 | 159689 | 159689 | 0.109375 / 0.109375 |
| gva | 161469 | 161469 | 161469 |  |
| lat | 161469 | 161469 | 161469 | 1.3161459122557062e-07 / 1.3161459122557062e-07 |
| lon | 161469 | 161469 | 161469 | 1.319563835977533e-07 / 1.319563835977533e-07 |
| ltt | 160468 | 160468 | 160468 |  |
| mode_3a | 31687 | 31687 | 31687 |  |
| mops_version | 160468 | 160468 | 160468 |  |
| nacp | 161469 | 161469 | 161469 |  |
| nacv | 161469 | 161469 | 161469 |  |
| nic | 161469 | 161469 | 161469 |  |
| nic_baro | 161469 | 161469 | 161469 |  |
| pic | 161469 | 161469 | 161469 |  |
| sac | 161469 | 161469 | 161469 |  |
| sda | 161469 | 161469 | 161469 |  |
| sic | 161469 | 161469 | 161469 |  |
| sid | 161469 | 161469 | 161469 |  |
| sil | 161469 | 161469 | 161469 |  |
| sils | 161469 | 161469 | 161469 |  |
| tod_position | 161469 | 161469 | 161469 | 0.0070625000007567 / 0.0070625000007567 |
| tod_report | 161469 | 161469 | 161469 | 0.0 / 0.0 |
| tod_velocity | 160320 | 160320 | 160320 | 0.0070625000007567 / 0.0070625000007567 |
| track_deg | 159689 | 159689 | 159689 | 0.002747070312523192 / 0.002747070312523192 |
| track_number | 161469 | 161469 | 161469 |  |

No item was present in a decoded record without the aircraft having that value.
