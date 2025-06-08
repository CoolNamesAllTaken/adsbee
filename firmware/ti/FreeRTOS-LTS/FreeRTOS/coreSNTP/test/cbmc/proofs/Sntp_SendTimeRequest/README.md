Sntp_SendTimeRequest proof
==============

This directory contains a memory safety proof for Sntp_SendTimeRequest.

To run the proof.
-------------

* Add `cbmc`, `goto-cc`, `goto-instrument`, `goto-analyzer`, and `cbmc-viewer`
  to your path.
* Run `make`.
* Open html/index.html in a web browser.

-------------

* Run `make arpa` to generate a Makefile.arpa that contains relevant build information for the proof.
* Use Makefile.arpa as the starting point for your proof Makefile by:
  1. Modifying Makefile.arpa (if required).
  2. Including Makefile.arpa into the existing proof Makefile (add `sinclude Makefile.arpa` at the bottom of the Makefile, right before `include ../Makefile.common`).
