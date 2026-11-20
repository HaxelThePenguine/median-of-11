Subject: Feedback on a Lean 4 certificate for eleven-input median selection

Dear Tejasvi Singh Tomar,

I’m Rocco Martino, a master’s student in Cybersecurity at Politecnico di Torino. I’m working on a computer-assisted proof that Dobbelaere’s 25-comparator median network on eleven inputs is size-optimal. Your work on extreme paths in selection and sorting networks motivated me to look more closely at how the deletion argument interacts with a finite exclusion certificate.

In our model, boundary layers force an extreme to pass through three comparators. Deleting it twice leaves two nine-wire bounds, up to duality. Lean 4 checks the upper witness, the structural steps and the soundness of the replay rules. The two nine-wire bounds remain hypotheses of the final Lean theorem. The full certificate has been replayed computationally with independent Python and C++ checkers.

I would particularly welcome scrutiny of the memoization rule. A completed exclusion is attached to the pair of image sets up to one common wire permutation and an available suffix budget. The earlier prefix may have different extreme traces, so the proof transfers a proposed suffix back to the earlier prefix before invoking its exclusion. Do you see a gap in that argument or in the statement of the rank-deletion invariant?

Paper and sources: https://github.com/HaxelThePenguine/median-of-11/pull/1

Earlier archived candidate: https://doi.org/10.5281/zenodo.24397716

Best regards,

Rocco Martino
