# Execution record for 1.0.0-rc.3

The candidate extends Git commit 0b5d0a32eda56327b504344ed3d949957a72e0a7, the v1.0.0-rc.2 archive reference. The current reviewed Git tree is identified by the enclosing commit. [Source and artifact hashes](rc3-hashes.sha256) cover the Lean project, checkers, manuscripts and supporting files in this candidate. The published [certificate hashes](proof.sha256) continue to bind the original 26 gzip streams, the manifest and the JSON witness.

## Completed executions

Local observations on 20 November 2026. Times are elapsed seconds and vary with machine and load.

| Command | Exit | Time | Observation |
|---|---:|---:|---|
| bash scripts/verify.sh | 0 | 15.590 | Full regression audit. |
| c++ -std=c++20 -O2 -Wall -Wextra -Wpedantic -Werror verification/independent/check.cpp -lz -o ../validation/check | 0 | 2.337 | Independent reader compiled. |
| ../validation/check certificate | 0 | 0.154 | All 26 claims. |
| python3 -O check_certificate.py | 0 | 6.236 | All 26 claims. |
| bash scripts/evaluate-lean-archive.sh | 0 | 76.022 | All 26 accepted by the executable Lean replay. Its output matched Python and C++ byte for byte. |
| python3 lower.py --output ../regen/certificate | 0 | 1.087 | All regenerated archive files and generator stdout byte-identical in this environment. |
| python3 verification/tests/witness.py | 0 | 0.525 | All 2,048 Boolean and 177,147 ternary inputs. Each of the 25 individual gate deletions failed. |
| python3 verification/tests/history.py | 0 | 0.319 | Archived experiment records and witnesses agreed with their generators and validators. |
| bash scripts/verify-lean.sh | 0 | 124.492 | Clean Lean 4.19.0 build. See the axiom audit for the checked conditional result. |
| (cd formal && lake env lean -t=0 Audit.lean) | 0 | 1.469 | Independent axiom query with trust level zero. |
| bash scripts/build-paper.sh | 0 | 10.665 | Fresh PDF and bibliography plus a one-page reviewer summary. |
| CFF 1.2.0 Draft 7 schema validation | 0 | <1 | Software citation and preferred manuscript citation validated. |

Python and C++ accepted all 174,008 proof nodes. The archived-certificate checks rejected 25 targeted mutations and 32 seeded illegal-byte mutations. Both checkers agreed on 32 substitutions with legal opcodes, of which two supplied valid alternative proofs. Independent reverse-function search recovered all 20 rank optima across widths two through six. The deletion and structure experiments are documented in the historical and current review reports.

Toolchain observed locally was Python 3.12.14, GCC/G++ 14.2.0, Lean 4.19.0 commit 6caaee842e94, pdfTeX 1.40.26 from TeX Live 2025/dev, and Latexmk 4.86. The TeX format was generated from the installed TeX Live distribution because the preinstalled binaries lacked a registered format. PDF links, page count and final logs were checked after a fresh BibTeX build.

## Attempted kernel checks of the principal claims

A direct `decide +kernel` attempt for the 167,917-node replay at width nine and rank four ended with exit 137 after 60.587 s. The analogous baseline attempt for rank five ended with exit 137 after 37.766 s. Retrying rank five with packed row sets and a 6,000,000 KiB process limit produced `INTERNAL PANIC: out of memory`, exit 1 after 30.357 s. These are resource failures in the trial environment. The packed rank-four retry also ran out of memory at the same process limit, exiting 1 after 32.270 s. Both claims were accepted by the executable Lean replay and the two independent readers.

Reproduce the isolated attempts with `formal/Replay9Rank4.lean` and `formal/Replay9Rank5.lean` after generating the complete Lean input. The first 11 archive claims and the upper-bound witness are part of the successful default Lake build. The pinned Linux Lean archive SHA-256 is in `verification/lean/toolchain.sha256`.

## GitHub Actions

The workflow runs computational replay, a fresh manuscript and summary build, and the formal build with an executable Lean cross-check. Check the workflow on the exact candidate commit through the [PR checks](https://github.com/HaxelThePenguine/median-of-11/pull/1/checks). These jobs certify the scope recorded in the [formal verification report](formal-verification.md).

The initial rc.3 workflow detected a 2.49 pt overfull proof line with the Ubuntu runner’s TeX distribution. The proof opening was reflowed and the committed PDF was rebuilt. The mathematical argument and all proof sources remained the same.
