# CC1312 Firmware

## Documentation

[CC13x2 Proprietary RF User's Guide](https://software-dl.ti.com/simplelink/esd/simplelink_cc13x2_sdk/2.30.00.45/exports/docs/proprietary-rf/proprietary-rf-users-guide/proprietary-rf-guide/index-cc13x2.html)
* [Sync Word](https://software-dl.ti.com/simplelink/esd/simplelink_cc13x2_sdk/2.30.00.45/exports/docs/proprietary-rf/proprietary-rf-users-guide/proprietary-rf/packet-format.html?highlight=sync)

[CC1312 Technical Reference Manual](https://www.ti.com/lit/ug/swcu185g/swcu185g.pdf)

Helpful Threads
* [Simplelink Partial Rx](https://e2e.ti.com/support/wireless-connectivity/sub-1-ghz-group/sub-1-ghz/f/sub-1-ghz-forum/1295007/cc1352p7-partial-entry-mode-with-repeats-setting-new-packet-length?tisearch=e2e-sitesearch&keymatch=partial%252520receive#)
* [Checking status of PropRF RX Commands](https://e2e.ti.com/support/wireless-connectivity/sub-1-ghz-group/sub-1-ghz/f/sub-1-ghz-forum/942531/cc1310-how-do-i-use-rf_getinfo-to-find-out-if-the-command-issued-using-rf_postcmd-has-been-executed-or-in-queue)

## Helpful Info

* Don't let the debugger make more than 4 breakpoints. For some reason JLink's attempts to store flash breakpoints wreaks havoc on the CC1312 and scrambles values in the watch panel on Cortex Debug.
* Don't attempt to load firmware using the JLink debugger for the CC1312. Load firmware via the RP2040 instead, then attach the JLink debuger to the CC1312.