# t-0556: /metrics message sizes, PR #348 vs main

Bench: ADSBee 1090U (pi-1), ten feeds with 63-character `.invalid` URIs (0-4 BEAST/TCP, 5-9 BEAST/UDP, because the 32 kB feed RAM budget fits only five TCP feeds), FEED_ENABLE=1, runtime WiFi station, 40 s capture of `ws://<ip>/metrics`. Buffer: `kNetworkMetricsMessageMaxLen` = 2048 B (max 2047 B of text).

| Image | Messages in 40 s | Message | Size (B) | Valid JSON |
|---|---|---|---|---|
| main fa6dc304 | 41 | single combined message | 2047 (every one truncated) | 0 of 41 |
| PR 6a3424eb | 41 | 1: `aircraft_dictionary_metrics` + `server_metrics` | 1562 | 41 of 41 |
| PR 6a3424eb | 40 | 2: `device_status` | 821 | 40 of 40 |

Worst-case bounds for the PR, from the captured messages:
- Message 1, with every integer at the uint32 maximum (10 digits): 1968 B, so 79 B of headroom.
- Message 2, with every number at its widest, a 63-character NTP server, a 32-character version (the real limit is 23) and the state `downloading`: 1106 B.
