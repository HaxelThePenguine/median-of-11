# Median of eleven in 25 comparators

How small can a fixed circuit be if it only has to return the middle of eleven numbers? In the compare–exchange model, **25 comparators suffice and 24 are impossible**. This repository pairs a published 25-comparator circuit with a reproducible finite certificate for the lower bound.

Each operation on wires `i < j` sends the smaller input to `i` and the larger to `j`. Wire 5 (numbering from zero) must return the sixth smallest input for every totally ordered input tuple, including ties. The objective counts comparators. Depth is unrestricted.

[Manuscript (PDF)](paper/main.pdf) · [LaTeX source](paper/main.tex) · [Critical review](docs/review-report.md) · [Reproducibility record](docs/reproducibility.md)

The audited research artifact is version **1.0.0-rc.1**. Two implementations replay all 26 claims. A separate search computes every rank optimum through width six from complete Boolean truth tables. Lean 4 checks the boundary-layer implication. The analytic deletion and full transcript soundness proofs are in Sections 4 and 5 of the manuscript.

Run the full computational audit with `bash scripts/verify.sh` (Python 3.10+, C++20, zlib development headers and standard Linux shell utilities). Build the paper with `cd paper && latexmk -pdf main.tex`. The original verification commands below remain supported.

[Original English research note](PAPER.md) · [Dimostrazione in italiano](PROOF.md) · [Certificate encoding](docs/certificate.md)

## Verify the result

Run these commands from the repository root with Python 3.10 or later. Verification uses the standard library.

```sh
python3 verify.py median11_25.json
python3 check_certificate.py
```

The first prints `n=11 size=25 errors=0/2048 first=[]`. The second ends with `ACCEPT median(11) >= 25; 174008 proof nodes`. The two checks establish different halves of the result.

| Evidence | What the program checks |
|---|---|
| [Network](median11_25.json) and [scalar verifier](verify.py) | Executes the circuit on all binary inputs. Thresholding commutes with compare–exchange, extending the result to arbitrary ordered values. |
| [Certificate](certificate/claims.json) and [checker](check_certificate.py) | Replays 26 finite exclusions, from two inputs through eleven. Earlier checked bounds can be used at larger widths. |
| [Proof and pruning rules, in Italian](PROOF.md) | Justifies boundary layers, extreme-input deletion, wire relabelling and reuse of completed subproblems. |
| [Search experiments and commands, in Italian](EXPERIMENTS.it.md) | Reproduces local resynthesis, annealing, exact repair and the global SAT attempts. The unrestricted SAT runs returned unknown. |

## Why the lower bound works

Suppose a circuit with 24 comparators computes the median. On the two binary layers with five and six ones, changing a single input bit across the boundary must change the designated output. Comparators preserve the number of ones and are monotone, so every other output stays fixed across that change. Moving between inputs on a layer by exchanging a zero and a one shows that the entire final configuration is constant on each layer.

Take the first comparator that reuses a wire. All earlier comparisons are disjoint. We can choose a global minimum or maximum that passes through the reused wire and encounters both comparisons. Its current wire depends on at most four original inputs. Those four can all be zero or all be one on the five-ones layer. The wire therefore varies on that layer and must participate in another comparison before it can be a final output.

Fix that extreme input permanently and remove its path. Every comparison it encounters becomes a fixed routing of the other value. This removes at least three comparators. After removal, wires may be relabelled and comparator outputs may have either orientation. The lower-bound argument allows both orientations and any output wire. The same reasoning applies at width ten.

| Remaining inputs | Required rank (one-based) | Maximum comparators if 24 sufficed |
|---|---|---|
| 11 | 6 | 24 |
| 10 | 5 or 6 | 21 |
| 9 | 4, 5 or 6 | 18 |

Each of the three final ranks requires at least 19 comparators. The certificate checks the smaller-width bounds as well. This gives the contradiction and the lower bound of 25.

## Reproduce the self-review

```sh
python3 verify.py
python3 corruption.py
python3 audit_small.py
python3 lower.py --output rebuilt > rebuilt.jsonl
python3 -O check_certificate.py rebuilt
```

The review regenerated the proof from the distributed sources and compared it with the supplied certificate. It also tested truncated proof data, an invalid cache reference and a damaged circuit. An additional breadth-first search recomputed all eight listed claims through five inputs without extreme-path pruning, memoised proof references or the certificate. A separate check exercised 720 permutations of six varying values among eleven distinct keys.

Three points matter when auditing the checker. A frozen wire may be discarded only if a previously established smaller-width bound forbids touching it again. Cached exclusions must compare the actual sets of outputs under one common wire permutation. Finally, the indirect lower bound must survive arbitrary orientations after deleting a sentinel wire. The checker and the proof address these conditions explicitly. Generator and checker are separate implementations developed in the same AI-assisted project. External review and historical priority remain open.

## Attribution

The 25-comparator construction is listed by Bert Dobbelaere. A November 2026 report gives the relevant nine-input selection bounds. The repository supplies its own finite checks for those bounds. [Dobbelaere’s median networks](https://bertdobbelaere.github.io/median_networks.html) · [Nine-input results](https://generalised.si/research/moore-bound-defect-two)

## Licensing

Original software, verification tools,
Lean formalization and certificates:
MIT License (LICENSE).

Original manuscript, LaTeX source
and figures: CC BY 4.0
(LICENSE-PAPER.md).

Third-party material is excluded
from these grants where applicable.
The 25-comparator construction is
attributed to Bert Dobbelaere.

