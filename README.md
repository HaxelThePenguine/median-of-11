# Optimality of a 25-Comparator Median Selection Network on Eleven Inputs

A computer-assisted proof gives a matching lower bound for Bert Dobbelaere's published 25-comparator construction. The network is a fixed sequence of compare–exchange operations. Each pair `i < j` places the smaller value on wire `i` and the larger on wire `j`. Wire 5, numbered from zero, returns the sixth smallest input, including ties. The size bound allows arbitrary depth.

**Artifact version 1.0.1.** Lean 4.19.0 checks the exact-size theorem `Median11.median11_optimal` without certificate hypotheses. The kernel verifies the upper-bound witness, the reduction, and the decoded proof data for all 26 archived exclusions. Python, C++ and the Lean executable checker replay the complete computational certificate with matching results.

| Entry point | Start here |
|---|---|
| Read the paper | [PDF](paper/main.pdf) · [LaTeX](paper/main.tex) · [Bibliography](paper/references.bib) |
| Verify the mathematical theorem | [Proof and formal status](docs/formal-verification.md) · [Kernel build script](scripts/verify-lean.sh) |
| Verify the computational certificate | [Replay script](scripts/verify.sh) · [Format](docs/certificate.md) · [Claims](certificate/claims.json) |
| Inspect the Lean formalization | [Lean project](formal) · [Optimality statement](formal/Median11/Optimality.lean) |
| Reproduce the experiments | [Verification and environment](docs/reproducibility.md) · [Search experiments](EXPERIMENTS.it.md) |
| Review the result | [One-page summary](review/summary.pdf) · [Reviewer guide](review/README.md) · [Adversarial report](docs/review-report.md) |
| Cite this work | [Citation metadata](CITATION.cff) · [Archive versions](#archived-versions) |

## Reproduce the checks

On Linux, install Python 3.10+, a C++20 compiler, zlib headers, Lean 4.19.0, and LaTeX with `latexmk`. Run from the repository root.

```sh
bash scripts/verify.sh
bash scripts/verify-lean.sh
(cd paper && latexmk -pdf main.tex)
```

The computational audit checks all 2,048 binary inputs and all 177,147 ternary inputs, then runs two independent implementations of the lower-bound replay and compares their results. Both accept all 26 claims and report `ACCEPT median(11) >= 25; 174008 proof nodes`. It regenerates the certificate, checks adversarial mutations, and compares against an independent exhaustive calculation at widths two through six. The exact source relation between the catalogue witness JSON and Lean is checked by the Lean build script.

For individual runs, the original commands `python3 verify.py median11_25.json` and `python3 check_certificate.py` remain available. See [the verification record](docs/reproducibility.md) for additional commands.

## Why the lower bound works

Selecting the correct output bit forces every remaining output bit to be fixed within each boundary layer. At the first comparison that reuses a wire, the earlier comparisons are disjoint. One extreme input can traverse both comparisons. Its current output still varies on a balanced boundary layer, so a later comparison must touch its wire. Removing the extreme removes at least three comparators. Apply this reasoning at widths eleven and ten, then replay the exclusions of size 18 for ranks four and five at width nine. Rank six follows by duality. The lower-bound model allows either orientation and any fixed output wire throughout.

## Archived versions

Cite this artifact by its exact Git commit. The [stable 1.0.0 release](https://github.com/HaxelThePenguine/median-of-11/releases/tag/v1.0.0) and earlier DOI deposits identify distinct snapshots.

| Snapshot | Archive |
|---|---|
| `v1.0.0-rc.1` | [10.5281/zenodo.24397284](https://doi.org/10.5281/zenodo.24397284) |
| `v1.0.0-rc.2` | [10.5281/zenodo.24397716](https://doi.org/10.5281/zenodo.24397716) |
| All versions | [10.5281/zenodo.24397283](https://doi.org/10.5281/zenodo.24397283) |

## Attribution and licensing

Bert Dobbelaere published the [25-comparator construction](https://bertdobbelaere.github.io/median_networks.html#N11L25D11). The project contributes the matching lower-bound argument and verification artifact. Historical priority for the proof remains open. Development used substantial AI assistance.

Copyright © 2026 Rocco Martino for the original work. The [MIT License](LICENSE) covers original Python and C++ sources, Lean formalization, verification tools and computational certificates. [CC BY 4.0](LICENSE-PAPER.md) covers the original manuscript, LaTeX sources, figures and explanatory material. See [third-party notices](THIRD-PARTY.md) for the catalogue witness and its upstream license.
