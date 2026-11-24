# Twenty-five comparators are necessary and sufficient for the median of eleven

**Research note · 19 November 2026**

**Abstract.** A fixed sequence of compare–exchange operations can place the median of eleven inputs on a designated wire using 25 comparators. We prove the matching lower bound. The argument uses a constraint on the entire output vector that follows from specifying just one output. On either binary input layer adjacent to the median threshold, every output wire must be constant. This forces some global extreme to traverse at least three comparators. Deleting an extreme twice reduces a hypothetical 24-comparator network to a nine-input selection network of size at most 18. A finite certificate excludes each resulting rank. A standalone checker replays the smaller-width bounds from first principles.

## 1. Model and theorem

A comparator on wires $i<j$ sends their minimum to $i$ and their maximum to $j$. The sequence of pairs is fixed before the inputs are known. Rank is one-based in ascending order. Wire indices are zero-based. Inputs may coincide.

**Theorem 1.** The minimum number of comparators needed to place the sixth smallest of eleven inputs on wire 5 is **25**, with unrestricted depth.

For the lower bound, let $C(n,r)$ denote the minimum size when each comparator may send its smaller output to either endpoint and the network designer may choose the output wire. Both choices are fixed for the whole network. A lower bound in this larger class applies to the stated model. The larger class is convenient because removing an input can permute the surviving wires.

## 2. Selecting one rank fixes two entire output layers

Let $H_j$ be the set of binary vectors with exactly $j$ ones. For rank $r$, put $w=n-r$. The selected bit is zero on $H_w$ and one on $H_{w+1}$. These two layers suffice for verification. Coordinatewise monotonicity gives the selected bit at every other weight. For general ordered inputs, thresholding each coordinate commutes with both minimum and maximum. Any incorrect selected value can be separated from the correct one by a threshold, yielding a binary counterexample.

**Lemma 1 (boundary layers).** If a network selects rank $r$, its full output vector is constant on $H_w$ and constant on $H_{w+1}$. The two constant vectors differ exactly on the selected wire.

*Proof.* Take $x$ in $H_w$ and change one zero to one, obtaining $y$. Monotonicity gives $F(x)\leq F(y)$ coordinatewise. Each comparator preserves weight, so the two outputs differ in exactly one bit. The selected bit changes, identifying that bit uniquely. Now take two weight-$w$ inputs related by exchanging a zero and a one. Their coordinatewise maximum is a common upper neighbour in $H_{w+1}$. Clearing the selected bit of its output recovers both lower outputs, so they coincide. Such exchanges connect the entire lower layer. Every upper-layer input has a lower neighbour, which determines its output as well. ∎

## 3. Removing an extreme saves three comparators

**Lemma 2 (extreme path).** Suppose one of the two boundary layers contains at least four zeros and four ones per input. In every valid network, some input position can be assigned a global minimum or maximum whose path traverses at least three comparators.

*Proof.* Consider the first comparator that touches a previously used wire. Such a comparator must exist. Otherwise each final wire depends on at most two original inputs and varies on the specified layer: its dependencies can all be set to zero, or all to one, while preserving the layer weight. This contradicts Lemma 1.

Before this first reuse, the comparators are pairwise disjoint. Choose a reused wire. If it carried the smaller output of its earlier comparator, put a unique global minimum at one input of that comparator. If it carried the larger output, use a unique global maximum. This extreme traverses both the earlier comparator and the first reuse. Immediately afterwards the wire carrying it depends on at most four original inputs. Its Boolean function takes both values on the specified layer, by assigning those dependencies all zeros or all ones. If the wire were never touched again, it would still vary at the output. Lemma 1 therefore forces a third comparison on the wire. The route of a unique extreme is fixed by the wiring, so it traverses that comparison. ∎

Fix the chosen input to a sentinel smaller or larger than all ordinary values. Its route is now deterministic. At each comparison along that route, the ordinary value passes to a known output. Deleting the sentinel and reconnecting these ordinary wires removes one comparator per encounter. Relabelling wires absorbs the fixed routing. For an interior rank, removing a minimum changes the requested rank to $r-1$, while removing a maximum leaves it at $r$. Under the hypothesis of Lemma 2 this gives

$$
C(n,r)\ \geq\ 3+\min\{C(n-1,r-1),C(n-1,r)\}.
$$

**Proof of Theorem 1.** The weight-five layer satisfies Lemma 2 for $(11,6)$ and for both ten-input problems obtained after one deletion. Applying the inequality twice gives

$$
C(11,6)\ \geq\ 6+\min\{C(9,4),C(9,5),C(9,6)\}.
$$

The certificate described below proves a lower bound of 19 for the fourth and fifth ranks on nine inputs. Complementing the bits and interchanging low and high comparator outputs gives the same bound for the sixth rank. Hence $C(11,6)\geq25$. For the upper bound, Dobbelaere lists a [25-comparator network](median11_25.json) in the required orientation. Direct evaluation on all 2,048 binary inputs gives the required bit on wire 5 in every case. The threshold argument extends this construction to all ordered inputs. ∎

## 4. Finite certificate and verification

Each claim $(n,r,L)$ excludes networks of size at most $L$. The checker processes claims in order, using only previously verified smaller-width bounds or the trivial lower bound zero. At a search node, $A$ and $B$ are the sets of distinct outputs reached from the two boundary layers by the current prefix. The checker first tests whether any wire already separates the layers. The following rules justify the exclusions.

| Rule | Justification |
|---|---|
| Image size | One comparator has at most two preimages per output. With $k$ steps left, a layer with more than $2^k$ images cannot collapse to the singleton required by Lemma 1. |
| Extreme paths | If a specified extreme already meets $d$ comparators, deletion leaves at most $L-d$ for the reduced problem. Given a verified lower bound $b$, a path exceeding $L-b$ is impossible. At equality, its present wire must remain untouched, so variation on either boundary layer excludes the prefix. |
| Choice of next operation | Try every unordered pair. Reversing the orientation changes only the labelling seen by an arbitrary continuation. A comparison acting as one fixed permutation throughout the union of both images can likewise be absorbed into the continuation at zero cost. |
| Reuse of a completed exclusion | If one common wire permutation identifies both image sets with those of an already excluded subproblem, any successful continuation would transfer under that permutation. Reuse is valid when the earlier exclusion allowed at least as many remaining comparators. |

The [manifest](certificate/claims.json) contains 26 claims. The [checker](check_certificate.py) reconstructs the required branches and verifies their reasons for closure across 174,008 proof nodes. The generator represents layers as bitsets. The checker uses explicit sets and follows the extreme path from each possible original input separately. Both programs were developed in the same project. The global SAT search returned *unknown*; the finite combinatorial certificate supplies the lower bound.

Run from the repository root with Python 3.10 or later:

```sh
python3 verify.py median11_25.json
python3 check_certificate.py
```

The expected final lines are `n=11 size=25 errors=0/2048 first=[]` and `ACCEPT median(11) >= 25; 174008 proof nodes`, respectively. [Regeneration commands and additional checks](docs/reproducibility.md) are included for readers auditing the computation.

## Sources and status

Bert Dobbelaere's catalogue supplies the eleven-input construction. A report dated 16 November 2026 lists the nine-input selection bounds used in Section 3. The accompanying certificate checks those bounds separately. This note reports a reproducible computational proof. External peer review and historical priority remain open.

1. Bert Dobbelaere. [Median selection networks for a given number of inputs](https://bertdobbelaere.github.io/median_networks.html).
2. Generalised Superintelligence. [Graphs two below the Moore bound, and the median of nine inputs](https://generalised.si/research/moore-bound-defect-two), 16 November 2026.
