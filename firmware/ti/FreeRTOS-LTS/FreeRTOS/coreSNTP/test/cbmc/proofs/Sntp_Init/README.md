Sntp_Init proof
==============

This directory contains a memory safety proof for Sntp_Init.

The proof runs within 3 minutes on a t2.2xlarge. It provides complete coverage of:
 * Sntp_Init()

To run the proof.
-------------

* Add `cbmc`, `goto-cc`, `goto-instrument`, `goto-analyzer`, and `cbmc-viewer`
  to your path.
* Run `make`.
* Open html/index.html in a web browser.