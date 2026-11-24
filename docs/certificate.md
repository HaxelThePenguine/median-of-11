# Exclusion transcript, release profile 1

The archive certifies lower bounds for single ascending ranks. The ordered manifest is a JSON array of triples `[n,r,L]`. Acceptance means that every oriented network on those inputs with at most `L` comparators fails on every possible fixed choice of output wire (for each wire there is a counterexample). Each successful row contributes `L+1` to the available bounds. No numerical bound in the manifest is trusted before replay.

## Reader contract

The release serializes every rank from 1 to `(n+1)//2` at widths 2 through 9, then (10,5) and (11,6), in increasing lexicographic order. For each triple there is exactly one file `n-r.gz`. The independent reader requires the complete profile, one CRC-checked gzip member per file, no trailing bytes, and no unlisted files. Its limits are 1,000,000 bytes per file before and after decompression and budgets 0–30. Those implementation limits cover this artifact. A rejected file proves nothing. Other streams can encode valid derivations, so distribution hashes and logical acceptance serve different purposes.

Let `w=n-r`. Initially the two nonempty images contain all width-`n` words of weights `w` and `w+1`; bit zero is wire zero. Track budgets in **comparators**, including repeated comparisons. At each node exclude immediate success before checking a reason. A separator bit is absent from the OR of the lower image and present in the AND of the upper image.

| Byte | Payload checked by the reader |
|---:|---|
| 0 | Expand with positive remaining budget. Visit every required child in lexicographic order of (minimum port, maximum port), with minimum port smaller. After every child closes, record this node's common key and largest proved budget. |
| 1 | Either image has cardinality strictly greater than two raised to the remaining budget. |
| 2 | The common key occurs in this claim's table of completed expansions with at least this much budget. References have no explicit index. |
| 3 | At least one input's minimum or maximum trace has reached its allowance and ends on a wire varying within one layer. |

For a candidate pair both discordant patterns must occur somewhere in the union of the two images. Simulate the minimum going to the first endpoint. If any extreme would exceed its allowance, omit this child. Otherwise push the gate, reduce the remaining budget by one, and consume its subtree. A child has no length field. The reader determines its extent recursively. End of input must coincide with closure of the root. Blocked branches carry no byte, making recomputation of the complete candidate set part of the trust boundary.

For sign minimum use reduced rank `r-1`, for maximum use `r`. A valid rank `t` at width `n-1` has dual representative `min(t,n-t)`. Subtract the previously checked lower bound for this representative from the root budget. For a missing lower bound or an out-of-range reduced rank subtract zero. The Python generator may propose bounds from its static table; neither replay uses that table. Tables of closed residual states are private to one claim.

## Common key

For each wire form the ordered pair of column sums on the two images, counting each distinct row once. Stable-sort the wires by this pair, retaining ascending input index at ties. Apply this one permutation to all rows. Store the complete sets. Sorting by sums supplies a reproducible labelling, not a complete isomorphism test. Equal keys always exhibit an isomorphism. An undetected isomorphism only increases work. In C++ the normalized sorted union encodes both layers injectively because their weights differ.

## Proof obligations

The manuscript proves the rules in Section 5. In particular, a trace is evidence about one prefix. A closed cache entry asserts the absence of **any separating suffix** for the image pair with a stated budget. If a suffix separated the same images reached with different traces, conjugating it and attaching it to the prefix whose exclusion was proved would contradict that exclusion. Neither generator nor reader may publish an in-progress node as a completed exclusion.

The critical (9,4,18) stream has 10,529 expansions, 10,199 size leaves, 58,965 references, and 88,224 frozen leaves. Across all claims there are 10,965 expansions, 10,494 size leaves, 60,438 references and 92,111 frozen leaves. The regenerated log records zero edge omissions **after** filtering out fixed permutations on account of an excessive next path. The frozen-node rule itself is heavily used. Generator cache digests in `verification/records/bounds.jsonl` are diagnostic and do not replace replay.
