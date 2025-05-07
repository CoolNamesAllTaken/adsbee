JSON_Iterate proof
==============

This directory contains a memory safety proof for `JSON_Iterate`.
The proof runs in a few seconds and provides 100% coverage.

For this proof, the following functions are replaced with function contracts.
These functions have separate proofs.
* `skipAnyScalar`;
* `skipCollection`;
* `skipSpace`;
* `skipString`.

To run the proof.
* Add `cbmc`, `goto-cc`, `goto-instrument`, `goto-analyzer`, and `cbmc-viewer`
  to your path;
* Run `make`;
* Open `html/index.html` in a web browser.
