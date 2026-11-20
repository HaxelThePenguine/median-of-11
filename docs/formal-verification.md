# Formal verification in Lean 4.19.0

The Lean kernel proves `Median11.median11_optimal` without premises about certificate acceptance. In the standard-orientation model with output fixed to wire 5, a network of 25 comparators exists and every network that selects the sixth rank has at least 25 comparators. `Median11.median11_lower` gives the lower bound for either comparator orientation and any fixed output wire. Its Boolean-domain statement suffices for networks that must work on all inputs. The witness theorem `Median11.published_selects` holds over every decidable total order, including inputs with ties.

| Lean declaration | Kernel-checked result |
|---|---|
| `published_size`, `published_standard`, `published_binary`, `published_selects` | Dobbelaere's 25-comparator witness, its Boolean correctness on all 2,048 inputs, and its extension to decidable total orders. |
| `verify_replay_sound` | Successful preorder replay implies the size bound when the incidence bounds are supplied by theorems. |
| `PackedReplay.checkJob_sound`, `PackedReplay.checkJobs_sound` | A checked expansion establishes a residual exclusion. A checked block exports valid exclusions given valid imports. |
| `bound_7_3`, `bound_7_4`, `bound_8_3`, `bound_8_4`, `bound_8_5` | The prerequisite incidence bounds, including rank five on eight wires by duality. |
| `bound_9_4`, `bound_9_5` | Each rank needs at least 19 comparators on nine wires. |
| `median11_lower`, `median11_optimal` | The eleven-wire lower bound and exact size. |

## Certificate replay

The build checks all 19 archive claims through width eight and the two required nine-wire claims. The list-based checker covers the claims through width seven and the first three eight-wire ranks. The packed checker covers `8-4`, `9-4` and `9-5`, containing 4,947, 167,917 and 171 opcodes respectively. The full executable Lean replay also covers the remaining archive claims, with matching Python and C++ results across all 26 claims and all 174,008 proof nodes.

The block generator reads the original gzip members and records expansions in postorder so that all child and reference dependencies have finished before an expansion is certified. It preserves each opcode and preorder offset. The generator validates coverage and reconstructs each expansion's original interval. The kernel checks the transition to every child, the cursor at the end of each expansion, and the root interval. A reference supplies an earlier expansion offset and a swap list. The kernel checks that its interval has closed, its bound suffices, and both renamed image layers contain the corresponding rows of the earlier exclusion.

A row is represented by its binary wire pattern, and a set of rows by the natural number whose set bits are its rows. The packed checker proves the correspondence between mask operations and the original row-list semantics. In particular, the kernel checks the output layers of a supplied prefix, sparse witnesses for cardinality, and explicit paths for the two incidence rules. The rooted exhaustive-expansion lemma covers useful comparators in both orientations. Generated hints and intermediate layer masks are checked before the final proof uses them. Checking the closed Boolean statements in separate modules bounds the peak memory of the large replay. The proof composition then discharges every imported exclusion from earlier certified blocks.

## Reproduction and foundations

Run from the repository root with Lean 4.19.0 and Python 3.10 or newer.

```sh
bash scripts/verify-lean.sh
bash scripts/evaluate-lean-archive.sh
bash scripts/verify.sh
```

The first command generates the block modules, checks the witness and small replay data against their source artifacts, runs a clean Lake build, and audits the transitive axioms. The second executes the full Lean replay for comparison with the standalone readers. The third verifies the certificate and witness hashes, independently checks the archive with Python and C++, tests corrupted inputs, and regenerates the original proof streams.

The final lower bound and exact-size theorem depend on `propext`, `Classical.choice` and `Quot.sound`, as reported by `#print axioms`. The CI gate accepts only these standard Lean foundations and requires reports for the concrete nine-wire bounds and both final theorems. Every block is verified with `decide +kernel`. The project relies on Lean core and Std.

The [release-candidate verification record](rc3-validation.md) describes the earlier monolithic replay attempts and the formal scope of version 1.0.0-rc.3.
