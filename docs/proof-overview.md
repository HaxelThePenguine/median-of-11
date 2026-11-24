# Proof overview

The result concerns a fixed sequence of compare-exchanges on eleven inputs. A standard comparator sends the smaller value to the lower-numbered wire. The selected value is the sixth smallest, with multiplicity, on wire 5 in zero-based numbering. Dobbelaere's construction uses 25 comparators. The matching lower bound concerns the larger class in which each gate can have either orientation and the output may be any fixed wire.

## Two boundary layers

For ascending rank $r$ on $n$ binary inputs, the selected bit changes from zero to one as the number of ones goes from $w=n-r$ to $w+1$. Correctness on those two layers implies correctness on every Boolean input by monotonicity. Thresholding commutes with min and max, so this also checks the witness on ordered inputs with ties. Two distinct values in any fixed total order suffice to transfer the Boolean lower bound to that order.

A network preserves weight and is coordinatewise monotone. If one input bit changes from zero to one across the two layers, the outputs differ in exactly one bit, on the selected wire. Two weight-$w$ inputs related by exchanging a zero and a one have a common upper neighbour of weight $w+1$. Their output vectors therefore coincide. Such exchanges connect the entire lower layer, and each input in the upper layer has a lower neighbour. Every output wire is consequently constant on each layer.

## Deleting two extremes

Consider the first comparator that reuses a wire. The preceding gates form a matching. By choosing either a unique global minimum or a unique global maximum at an appropriate input, an extreme traverses both the earlier gate and the first reuse. The wire carrying it now depends on at most four original inputs. A boundary layer with at least four zeros and four ones admits assignments that set those inputs all to zero or all to one. This forces a later gate to touch the wire, since its final value has to be constant on the layer. The same argument rules out a network of disjoint gates.

The route of a strict extreme is fixed. Deleting the input and the gates on its route leaves a network on one fewer wire, with a moving bijection carrying the surviving labels. The new rank decreases by one for minimum deletion and stays the same for maximum deletion. At widths eleven and ten the relevant layers are sufficiently balanced. Thus a 24-comparator counterexample would give an 18-comparator network selecting rank four, five or six on nine wires.

## Finite exclusions

The certificate excludes size 18 for ranks four and five on nine wires. Reversing ranks by complementing bits and switching gate orientations covers rank six. The lower bound is therefore $19+3+3=25$.

A replay follows both layer images through prefixes. It checks that every useful next comparison is covered and verifies every closing reason, including cardinality, exhausted extreme routes and reuse of an already closed exclusion under a common wire permutation. The cache concerns the residual image pair and remaining budget. It can be reused even when the two prefixes have different extreme routes.

See the [manuscript](../paper/main.pdf) for the proofs, the [certificate format](certificate-format.md) for the replay rules and the [formalization guide](formal-verification.md) for the Lean declarations.
