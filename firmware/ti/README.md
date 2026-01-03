# CC1312 Firmware

## Documentation

[CC13x2 Proprietary RF User's Guide](https://software-dl.ti.com/simplelink/esd/simplelink_cc13x2_sdk/2.30.00.45/exports/docs/proprietary-rf/proprietary-rf-users-guide/proprietary-rf-guide/index-cc13x2.html)
* [Sync Word](https://software-dl.ti.com/simplelink/esd/simplelink_cc13x2_sdk/2.30.00.45/exports/docs/proprietary-rf/proprietary-rf-users-guide/proprietary-rf/packet-format.html?highlight=sync)

[CC1312 Technical Reference Manual](https://www.ti.com/lit/ug/swcu185g/swcu185g.pdf)

Helpful Threads
* [Simplelink Partial Rx](https://e2e.ti.com/support/wireless-connectivity/sub-1-ghz-group/sub-1-ghz/f/sub-1-ghz-forum/1333553/cc1310-fail-to-receive-long-250-bytes-wmbus-packets-and-rf_runimmediatecmd-cmd_prop_set_len-return-rf_statcmddoneerror)
* [Checking status of PropRF RX Commands](https://e2e.ti.com/support/wireless-connectivity/sub-1-ghz-group/sub-1-ghz/f/sub-1-ghz-forum/942531/cc1310-how-do-i-use-rf_getinfo-to-find-out-if-the-command-issued-using-rf_postcmd-has-been-executed-or-in-queue)
* [CC1310 Partial Receive Example](https://e2e.ti.com/support/wireless-connectivity/sub-1-ghz-group/sub-1-ghz/f/sub-1-ghz-forum/689154/cc1310-require-partial-mode-example-of-cc1310?CC1310-Require-Partial-Mode-Example-of-CC1310)
* [Partial Rx mode is not compatible with repeat mode](https://e2e.ti.com/support/wireless-connectivity/sub-1-ghz-group/sub-1-ghz/f/sub-1-ghz-forum/1321678/cc1310-wireless-m-bus-back-to-back-rx)

## Helpful Info

* Don't let the debugger make more than 4 breakpoints. For some reason JLink's attempts to store flash breakpoints wreaks havoc on the CC1312 and scrambles values in the watch panel on Cortex Debug.
* Don't attempt to load firmware using the JLink debugger for the CC1312. Load firmware via the RP2040 instead, then attach the JLink debugger to the CC1312.
