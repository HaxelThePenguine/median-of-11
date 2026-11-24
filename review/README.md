# External reviewer guide

Rocco Martino · Artifact version 1.0.3

Read the [one-page summary](summary.pdf) and the [manuscript](../paper/main.pdf). The contribution is a matching lower bound for Dobbelaere's 25-comparator witness at unrestricted depth.

1. Review the Boolean cover argument in Section 3 and the [boundary-layer lemma](../formal/Median11/ConcreteBoundary.lean).
2. Check the support bound at the first reuse of a wire in Section 4 and the [three-comparison lemma](../formal/Median11/ExtremePath.lean).
3. Follow the moving wire bijection in the [sentinel deletion proof](../formal/Median11/Deletion.lean).
4. Inspect the scope of a cached residual exclusion in the [packed replay](../formal/Median11/PackedReplay.lean) and [pruning lemmas](../formal/Median11/Pruning.lean). Section 5 of the paper explains why the earlier prefix may have different extreme routes.
5. Trace the nine-wire exclusions and rank duality through the [lower bound](../formal/Median11/LowerBound.lean) and [optimality theorems](../formal/Median11/Optimality.lean).

The [reproduction guide](../docs/reproducibility.md) gives the build and replay commands. The [validation notes](../docs/validation.md) describe which properties the implementations check and how the original archive relates to the Lean input. Cite the Git commit used. External human peer review and historical priority remain open.
