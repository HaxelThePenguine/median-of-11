# Reproducing the median-of-eleven audit

The original proof inputs are from Git commit `9ae024e5b5ecda05960c6e14d5875f9c099f3c98`. This revision preserves the original generator, Python checker, streams, construction and experimental logs. The research artifact version is **1.0.0-rc.1**. An exact Git revision and the checksum of its exported archive identify a particular snapshot.

## Full computational verification

From the repository root on Linux with Python 3.10+, a C++20 compiler and zlib development headers:

```sh
bash scripts/verify.sh
```

This includes all 26 claims in regular CI. It builds in a temporary directory, diff-checks Python and C++ output per claim, computes the exact small-width optima independently, runs the negative controls and regenerates every proof stream. It checks distributed compressed hashes before replay. During regeneration it compares decompressed bytes so legitimate differences in gzip headers across Python releases do not invalidate a logically identical proof.

For individual steps:

```sh
g++ -std=c++20 -O2 -Wall -Wextra -Wpedantic -Werror verification/independent/check.cpp -lz -o /tmp/median-check
python3 verify.py median11_25.json
python3 -O check_certificate.py
/tmp/median-check certificate
python3 lower.py --output rebuilt > rebuilt.jsonl
python3 -O check_certificate.py rebuilt
/tmp/median-check rebuilt
g++ -std=c++20 -O2 verification/tests/backward.cpp -o /tmp/median-bfs
/tmp/median-bfs
python3 verification/tests/mutations.py /tmp/median-check
python3 verification/tests/structure.py
python3 verification/tests/witness.py
sha256sum -c docs/proof.sha256
```

Use a fresh or empty `rebuilt` directory. The independent reader expects only the manifest and its proof members there. A width- or rank-limited generator run is useful for experiments; the release reader checks the complete release profile. The original Python commands in the README continue to work.

## Observed runs, 20 November 2026

Debian 13, Linux x86-64, AMD EPYC 9V74, CPython 3.12.14, GNU C++ 14.2.0, zlib C header 1.3.1. Python reports zlib runtime 1.3.2. Times below are wall-clock observations on a shared host, including process startup. The JSON record gives the actual command-line argument arrays, exit statuses, output digests and per-claim node counts. All rows of the following table exited 0. [Run record](run-record.json)

| Check | Seconds | Observation |
|---|---:|---|
| Scalar witness | 0.029 | 0 errors on 2,048 binary inputs |
| Independent witness and gate deletions | 0.417 | 2,048 binary, 177,147 ternary, all 25 deletions detected |
| Published Python checker, optimized interpreter | 5.411 | 26 claims, 174,008 nodes |
| C++ release build / replay | 2.429 / 0.166 | Identical stdout to Python |
| Full certificate generation | 1.063 | 27 files byte-identical, diagnostic log identical |
| Rebuilt Python / C++ replay | 5.930 / 0.190 | Both accepted all claims |
| Reverse BFS, execution | 0.518 | All ranks on widths 2–6, including duals |
| Original small audit | 0.037 | Eight optima through width five and 720 distinct-value inputs |
| Full-vector deletion test | 0.426 | 407,160 comparisons against the unreduced circuits |
| Targeted and seeded mutation tests | 3.728 | 57 mandatory rejects and 32 legal-opcode cross-checks |
| Full shell workflow | 15.741 | Regeneration, cross-checks and negative controls passed |

The deletion test exhausts every oriented gate sequence on four wires of lengths zero to three, four sentinel positions, both signs and all ordinary triples over three values: $(1+12+12^2+12^3)\cdot4\cdot2\cdot27=407{,}160$. The reverse BFS compares complete one-output truth tables on the whole cube. Its outputs at width six were 5, 9, 10, 10, 9, 5.

The mutation seed was 110625. Of 32 legal-opcode substitutions, 30 were rejected and two were alternate valid closures. Both checkers agreed on all 32. Bytes rejected by the release profile include bad CRCs, trailing or missing bytes, an empty additional gzip member, duplicates, missing claims, invalid opcodes, and a manifest seeking the false bound of 26. A deliberately extended valid Python manifest duplicated (2,1), appended an empty gzip member to that stream and added an unlisted file. The original reader accepted with 174,009 nodes. This distinction concerns archival conformance, not mathematical soundness.

AddressSanitizer and UndefinedBehaviorSanitizer replayed the complete certificate with leak detection disabled and produced the same stdout. With the default sanitizer settings LeakSanitizer failed at process shutdown under the host tracer. Leak checking was not completed. Sanitizer runs assess the reader implementation, not theorem validity.

## Lean scope

```sh
lean --version
lean verification/lean/Boundary.lean
```

Lean 4.19.0 with the standard library checked `Boundary.edge` and `Boundary.rigidity` in under one second. The latter proves equality of the entire output (a selected bit and a list of remaining bits) on either boundary layer, for equal-width inputs. Its hypotheses are within-width monotonicity of the residual coordinates, weight preservation and the two specified bit values. The proof derives connectivity from arbitrary permutations, including swaps within a prefix. The kernel reports only `propext`, `Classical.choice` and `Quot.sound`. There are no project axioms, placeholders, native evaluation shortcuts or mathlib dependency. This development does not construct a comparator interpreter or formalize deletion, the pruning protocol or acceptance of the archive. The CI job checks the Lean distribution checksum.

## Manuscript and archive

A normal TeX Live installation needs AMS classes, TikZ, cleveref, booktabs, hyperref, BibTeX and latexmk. Build the manuscript and bibliography together:

```sh
cd paper
env SOURCE_DATE_EPOCH=1795132800 FORCE_SOURCE_DATE=1 TZ=UTC latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The PDF has nine pages. The fixed-epoch build was executed twice with pdfTeX 1.40.26, BibTeX 0.99d and latexmk 4.86. Both outputs had SHA-256 `5209c3bc574167e6016defa74fcaaaf1114f39bfc20a3e53c2cd6d69155c488c`. The final log had no unresolved citations, cross-references or overfull boxes. The TeX sources, the included figure and `main.bbl` are sufficient for a preprint source package. Across TeX distributions the PDF byte encoding can differ.

The audit host contained the TeX Live source tree but lacked the Debian-generated format and font map. An initial build failed to embed a font. For the successful runs the local setup used the following commands, in addition to the build command above. Normal TeX installations do not need them:

```sh
mkdir -p /tmp/median-audit/tex
cd /tmp/median-audit/tex
export TEXMF="{/tmp/median-audit/tex,/usr/share/texlive/texmf-dist,/usr/share/texmf}"
export TEXFORMATS=".:/tmp/median-audit/tex"
export TEXFONTMAPS="/tmp/median-audit/tex:"
cp /usr/share/texlive/texmf-dist/tex/generic/config/language.us language.dat
cat /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/*.map > pdftex.map
pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex pdflatex.ini
```

From the repository root, export the version recorded in a selected commit:

```sh
bash scripts/archive.sh /tmp/median-release HEAD
```

The ZIP contains the tracked files at that commit, including source, certificate, executable verification instructions, PDF and citation metadata. Its name includes the full commit ID and it has a SHA-256 sidecar. Use a commit ID when citing the artifact, since a branch can advance. Archival deposit, licensing and authorship approval are decisions for the rights holder. The repository had no license at the audited base. This revision does not grant a new redistribution license or assign a DOI.

## Historical experiments

With the Z3 shared library available, `python3 verification/tests/history.py` reconstructs archived job labels, checks the saved global SMT formula byte for byte, evaluates stored positive witnesses and checks annealing scores. We ran it successfully. The 94 small-window UNSAT entries, 2 wide-window UNSAT entries, 30 wide-window unknowns, 206 exact local exclusions and 4,048 repair exclusions are archival solver outcomes. We did not rerun those solvers. The unrestricted SAT attempts both ended unknown. None of these historical outcomes is used by the certificate.

## Current candidate

The sections above preserve the 1.0.0-rc.1 audit record. For 1.0.0-rc.3 use
[the current execution record](rc3-validation.md) and the
[Lean verification report](formal-verification.md).

```sh
bash scripts/verify.sh
bash scripts/verify-lean.sh
bash scripts/evaluate-lean-archive.sh
bash scripts/build-paper.sh
bash scripts/archive.sh /tmp/median-review
```
