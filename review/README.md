# External reviewer package

**Optimality of a 25-Comparator Median Selection Network on Eleven Inputs**

Rocco Martino · Version 1.0.1

- Read the [one-page review summary](summary.pdf) and [manuscript](../paper/main.pdf).
- The [repository](https://github.com/HaxelThePenguine/median-of-11) contains the sources. For an immutable reference, cite the exact Git commit. The [stable 1.0.0 release](https://github.com/HaxelThePenguine/median-of-11/releases/tag/v1.0.0) identifies the earlier kernel-checked optimality proof.
- The version-specific DOI [10.5281/zenodo.24397716](https://doi.org/10.5281/zenodo.24397716) identifies the immutable historical [v1.0.0-rc.2 snapshot](https://github.com/HaxelThePenguine/median-of-11/commit/0b5d0a32eda56327b504344ed3d949957a72e0a7).

## What to review

The proof rules out at most 24 comparators at unrestricted depth, giving a matching lower bound for Dobbelaere's 25-comparator witness. The most useful checks are the following.

1. Boundary-layer constancy keeps the full output vector fixed within each of the two threshold-adjacent weight layers. Review the Boolean cover proof in Section 3 and `boundary_constant` in [ConcreteBoundary.lean](../formal/Median11/ConcreteBoundary.lean).
2. At the first reuse of a wire, both gate inputs have combined support size at most four. The same boundary layer supplies all-zero and all-one assignments on that support. Review Section 4 and [three_comparisons](../formal/Median11/ExtremePath.lean).
3. Deletion removes a sentinel's comparisons while transporting the surviving values by a moving wire bijection. Verify that a valid interior rank still has an ordinary output. See [Deletion.lean](../formal/Median11/Deletion.lean).
4. A cached exclusion is about the residual suffix problem. The replay checks the common permutation and the completion of the earlier expansion before reuse. Verify the transition from an actual prefix to residual images in [PackedReplay.lean](../formal/Median11/PackedReplay.lean) and [Pruning.lean](../formal/Median11/Pruning.lean).
5. Trace the nine-wire bounds and rank duality through [LowerBound.lean](../formal/Median11/LowerBound.lean) and the exact-size theorem in [Optimality.lean](../formal/Median11/Optimality.lean).

## Verification

Use Python 3.10+, C++20 with zlib development headers, Lean 4.19.0, and LaTeX with latexmk.

~~~sh
bash scripts/verify.sh
bash scripts/verify-lean.sh
bash scripts/evaluate-lean-archive.sh
bash scripts/build-paper.sh
~~~

The first command runs both unannotated replays, rejects damaged certificates, compares independent small-width exact results, checks the witness and regenerates the proof streams. The second checks Lean proofs and prints transitive axioms. The third executes the Lean checker over all 26 claims. See the [dependency map and exact status](../docs/formal-verification.md) and [adversarial review](../docs/review-report.md).

Python and C++ are independent replay implementations within the same AI-assisted project. The independent reverse truth-table search covers all ranks at widths two through six. No external human referee has reviewed the proof or confirmed novelty. We welcome counterexamples, earlier references and scrutiny of the pruning rules and their transcription to Lean.
