# Technical validation

## Witness and certificate

The JSON witness has 25 standard-oriented gates with zero-based ports. The verification pipeline runs a scalar Boolean check and an independent bit-sliced check on all 2,048 binary inputs. It also runs all 177,147 ternary inputs and checks each single-gate deletion. The manuscript diagram is checked against the same witness.

The standalone Python and C++ replays independently parse the complete sequence of 26 exclusions. Python follows extreme inputs forwards and retains the two layer images as sets. C++ traverses prefix gates backwards to recover extreme routes and represents both layers by a sorted union. They agree claim by claim on the lower bounds and 174,008 total nodes. A third replay runs in Lean. The independent reverse truth-table search checks 20 ranks at widths two through six.

The regression suite rejects missing, reordered and duplicate claims, malformed JSON and gzip data, invalid opcodes and logically invalid pruning reasons. It also compares the two readers on in-alphabet opcode substitutions. Regeneration checks the manifest and every decoded proof stream against the distributed certificate.

## Formal proof and archive correspondence

Lean 4.19.0 checks the deductions on decoded certificate data and proves the witness, lower bounds and exact-size theorems. The kernel checks each supplied expansion and reference before use. The axiom audit permits only `propext`, `Classical.choice` and `Quot.sound`. See the [formalization guide](formal-verification.md) for the theorem inventory and the split between list and packed replays.

The SHA-256 check checks the distributed artifact bytes against the distributed manifest. Host tools handle gzip decoding, translation to Lean input and checks of correspondence to the archived opcode streams. The standalone readers provide separate checks of the gzip archive. All readers share the certificate specification.

## Scope

The result counts compare-exchanges at arbitrary depth, with a fixed network and output wire. The exact-size result applies to decidable total orders containing a strict pair, with multiplicities counted in the rank. Optimal depth, adaptive comparison cost and separate min/max costs are outside the theorem's scope.

The manuscript, implementation and validation were developed with substantial generative AI assistance. The standalone readers are independent implementations within the same project. External human peer review and historical priority remain open.
