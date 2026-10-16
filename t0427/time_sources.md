# ASTERIX time items with each time source

The recorded 49-minute sky capture used in [crosscheck.md](crosscheck.md) was replayed on the host through the
firmware's aircraft dictionary and ASTERIX encoder once per second while the time source changed: none (first
10% of rounds), network time from SNTP (simulated 40 ms ahead of true UTC), GNSS and network together (GNSS is
true UTC), then network only after the GNSS loss. The clock is set in the firmware's order: network first, then
GNSS. Both decoders read every record; expected times come from the capture timestamps, not from the encoder.

Decoders: asterix_decoder 0.7.11 (CAT021 2.6, CAT023 1.3) and libasterix 0.36.3 (CAT021 2.7, CAT023 1.3).
Tolerance: half an LSB (3.9 ms) plus 1.5 ms for the replay's millisecond rounding. 29,478 records, 0 mismatches.

| Time source | Field | Records | asterix_decoder agrees | libasterix agrees | Largest difference |
|---|---|---:|---:|---:|---|
| none | I021/040 NOGO = 1 | 2898 | 2898 | 2898 |  |
| none | I021/073 time | 2898 | 2898 | 2898 | 3.88 ms |
| none | I021/075 time | 2898 | 2898 | 2898 | 3.88 ms |
| none | I021/077 time | 2898 | 2898 | 2898 | 0.00 ms |
| none | I023/070 time of day | 297 | 297 | 297 | 0.00 ms |
| none | I023/100 NOGO = 1 | 297 | 297 | 297 |  |
| none | I023/100 TSV = 1 | 297 | 297 | 297 |  |
| network (SNTP) | I021/040 NOGO = 0 | 7697 | 7697 | 7697 |  |
| network (SNTP) | I021/073 time | 7697 | 7697 | 7697 | 3.88 ms |
| network (SNTP) | I021/075 time | 7634 | 7634 | 7634 | 3.88 ms |
| network (SNTP) | I021/077 time | 7697 | 7697 | 7697 | 2.50 ms |
| network (SNTP) | I023/070 time of day | 889 | 889 | 889 | 2.50 ms |
| network (SNTP) | I023/100 NOGO = 0 | 889 | 889 | 889 |  |
| network (SNTP) | I023/100 TSV = 0 | 889 | 889 | 889 |  |
| GNSS + network | I021/040 NOGO = 0 | 6761 | 6761 | 6761 |  |
| GNSS + network | I021/073 time | 6761 | 6761 | 6761 | 3.88 ms |
| GNSS + network | I021/075 time | 6700 | 6700 | 6700 | 3.88 ms |
| GNSS + network | I021/077 time | 6761 | 6761 | 6761 | 1.56 ms |
| GNSS + network | I023/070 time of day | 889 | 889 | 889 | 1.56 ms |
| GNSS + network | I023/100 NOGO = 0 | 889 | 889 | 889 |  |
| GNSS + network | I023/100 TSV = 0 | 889 | 889 | 889 |  |
| network after GNSS loss | I021/040 NOGO = 0 | 9159 | 9159 | 9159 |  |
| network after GNSS loss | I021/073 time | 9159 | 9159 | 9159 | 3.88 ms |
| network after GNSS loss | I021/075 time | 9153 | 9153 | 9153 | 3.88 ms |
| network after GNSS loss | I021/077 time | 9159 | 9159 | 9159 | 2.50 ms |
| network after GNSS loss | I023/070 time of day | 888 | 888 | 888 | 2.50 ms |
| network after GNSS loss | I023/100 NOGO = 0 | 888 | 888 | 888 |  |
| network after GNSS loss | I023/100 TSV = 0 | 888 | 888 | 888 |  |

- With GNSS present the times match true UTC, so GNSS replaced the 40 ms network offset in every round.
- Network time clears TSV and NOGO in CAT023 and the NOGO bit in CAT021 (I021/040 then has no second extension).
- No time source: times count from boot with TSV, NOGO and the I021/040 NOGO bit set, as before.
