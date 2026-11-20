# Optimality of a 25-Comparator Median Selection Network on Eleven Inputs

Exactly **25 comparators** are necessary and sufficient to select the sixth smallest of eleven inputs on wire 5, numbered from zero. The standard model uses a fixed sequence of compare–exchange operations, with each pair `i < j` sending the smaller value to wire `i`. The result allows arbitrary depth and includes inputs with ties. Bert Dobbelaere published the 25-comparator construction.

**Artifact version 1.0.1.** Lean 4.19.0 proves `Median11.median11_optimal` using the verified witness and lower bounds. The kernel checks the decoded proof data for all 26 archived exclusions, comprising 174,008 nodes.

| Entry point | Start here |
|---|---|
| Read the paper | [PDF](paper/main.pdf) · [LaTeX](paper/main.tex) · [Bibliography](paper/references.bib) |
| Verify the mathematical theorem | [Proof and formal status](docs/formal-verification.md) · [Kernel build script](scripts/verify-lean.sh) |
| Verify the computational certificate | [Replay script](scripts/verify.sh) · [Format](docs/certificate.md) · [Claims](certificate/claims.json) |
| Inspect the Lean formalization | [Lean project](formal) · [Optimality statement](formal/Median11/Optimality.lean) |
| Reproduce the experiments | [Verification and environment](docs/reproducibility.md) · [Search experiments](EXPERIMENTS.it.md) |
| Review the result | [One-page summary](review/summary.pdf) · [Reviewer guide](review/README.md) · [Adversarial report](docs/review-report.md) |
| Cite this work | [Citation metadata](CITATION.cff) · [Archive versions](#archived-versions) |

## Verify the theorem

From the repository root on Linux, run the kernel check with Python 3.10+ and Lean 4.19.0 (including `lake`) on your path. The repository pins the Lean version in [the toolchain file](formal/lean-toolchain).

```sh
bash scripts/verify-lean.sh
```

The script checks the certificate and witness hashes, generates the Lean replay data, runs a clean build, and audits the transitive axioms for every archived exclusion and the final theorem. For `Median11.median11_optimal`, expect `propext`, `Classical.choice` and `Quot.sound`. Lean checks the proof on the decoded data. The host tools check the gzip archive and the translation to Lean input. [Formal verification report](docs/formal-verification.md)

The recorded Windows build took about 12 minutes. [Reproducibility record](docs/reproducibility.md#local-verification-of-101)

## Replay the archive and build the paper

For the independent certificate audit, install a C++20 compiler and zlib headers alongside Python. To rebuild the paper and reviewer summary, install TeX Live with BibTeX and `latexmk`. Run from the repository root.

```sh
bash scripts/verify.sh
bash scripts/evaluate-lean-archive.sh
bash scripts/build-paper.sh
```

The first command checks the witness on all 2,048 binary and 177,147 ternary inputs, regenerates the certificate, tests adversarial mutations, and compares the Python and C++ replays. The second runs the Lean executable replay using the pinned toolchain. All three readers agree on the 26 claims and end with `ACCEPT median(11) >= 25; 174008 proof nodes`. The last command rebuilds the two PDFs.

For individual runs, the original commands `python3 verify.py median11_25.json` and `python3 check_certificate.py` remain available. See [the verification record](docs/reproducibility.md) for additional commands.

## Why the lower bound works

Selecting the correct output bit forces every remaining output bit to be fixed within each boundary layer. At the first comparison that reuses a wire, the earlier comparisons are disjoint. One extreme input can traverse both comparisons. Its current output still varies on a balanced boundary layer, so a later comparison must touch its wire. Removing the extreme removes at least three comparators. Apply this reasoning at widths eleven and ten, then replay the exclusions of size 18 for ranks four and five at width nine. Rank six follows by duality. The lower-bound model allows either orientation and any fixed output wire throughout.

## Archived versions

Cite this artifact by its exact Git commit. From the repository root, `bash scripts/archive.sh /tmp/median-review HEAD` exports the selected commit to a ZIP with a SHA-256 checksum. The [stable 1.0.0 release](https://github.com/HaxelThePenguine/median-of-11/releases/tag/v1.0.0) and earlier DOI deposits identify distinct snapshots.

| Snapshot | Archive |
|---|---|
| `v1.0.0-rc.1` | [10.5281/zenodo.24397284](https://doi.org/10.5281/zenodo.24397284) |
| `v1.0.0-rc.2` | [10.5281/zenodo.24397716](https://doi.org/10.5281/zenodo.24397716) |
| All versions | [10.5281/zenodo.24397283](https://doi.org/10.5281/zenodo.24397283) |

## Attribution and licensing

Bert Dobbelaere published the [25-comparator construction](https://bertdobbelaere.github.io/median_networks.html#N11L25D11). The project contributes the matching lower-bound argument and verification artifact. Historical priority for the proof remains open. Development used substantial AI assistance.

Copyright © 2026 Rocco Martino for the original work. The [MIT License](LICENSE) covers original Python and C++ sources, Lean formalization, verification tools and computational certificates. [CC BY 4.0](LICENSE-PAPER.md) covers the original manuscript, LaTeX sources, figures and explanatory material. See [third-party notices](THIRD-PARTY.md) for the catalogue witness and its upstream license.
