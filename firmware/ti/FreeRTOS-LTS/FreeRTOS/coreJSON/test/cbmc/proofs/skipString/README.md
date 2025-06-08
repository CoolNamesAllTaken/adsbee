skipString proof
==============

This directory contains a memory safety proof for `skipString`.
The proof runs in a few seconds and provides 100% coverage.

For this proof, the following functions are replaced with function contracts.
These functions have separate proofs.
* `skipEscape`;
* `skipUTF8`.

To run the proof.
* Add `cbmc`, `goto-cc`, `goto-instrument`, `goto-analyzer`, and `cbmc-viewer`
  to your path;
* Run `make`;
* Open `html/index.html` in a web browser.
