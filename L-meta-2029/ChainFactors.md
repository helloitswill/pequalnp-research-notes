# Intersecting ordered supergraphs to compute an edge function

Consider a bipartite graph with no four-cycle. Add edges so the neighbors of each right-hand vertex occupy an initial segment of one ordering of the left-hand vertices. The completed graph is a chain graph. Its full edge function can be computed in a single pass over the left-hand vertices followed by one test per right-hand vertex. Could several such circuits share work, with their answers combined by AND to recover the original edge function?

**Every exact circuit of this form has at most `2(s+1)` original graph edges, where `s` is its total number of fan-in-two gates.** This holds when all factors use the same left and right vertex sets, their full edge functions actually occur on circuit wires, and the conjunction agrees on every vertex subset. The circuits computing the factors may share gates. L-meta-2029 allows general monotone circuits, so the full problem remains open. [Lean source](ChainFactorBound.lean)

## A test case

For each field order `q`, take the `q²` affine points and `q²` nonvertical lines. At order three, nine orderings already suffice if the test selects exactly one point and one line: use one ordering per line with that line’s incident points first. Correctness on *all* selections requires exactly 36 orderings. This alone uses more distinct factor outputs than the 35 gates in the previously verified point-star circuit.

| Field order | Distinct unions of line neighborhoods | Minimum number of factors | Full inputs checked |
| --- | --- | --- | --- |
| 2 | 10 | 4 | 256 |
| 3 | 110 | 36 | 262,144 |

The program constructs both witnesses for optimality. A collection of point orders implements the claimed number of factors. An equally large family of pairwise incomparable unions proves that fewer cannot suffice. The program checks each witness, evaluates the resulting conjunction on the full truth table, and can export the orders and witnesses as JSON. [Certificate generator](chain_cover.py)

## Why the construction runs out of room

1. **When an ordering works.** Fix a selected set of right-hand vertices and let `N` be the union of their true neighborhoods. Within one completion the union grows to the smallest prefix containing `N`. Now select all left vertices outside `N`. This input has no original edge, so at least one factor must reject it. That factor’s prefix must be precisely `N`. Conversely, if each neighborhood union occurs as a prefix in some ordering, the conjunction is correct on all inputs. A single ordering can cover only a chain of nested unions, and a chain of unions extends to an ordering by appending successive set differences. The minimum number of orders is therefore the width of the family of neighborhood unions under inclusion. The last identification uses Dilworth’s theorem. [Dilworth, *A Decomposition Theorem for Partially Ordered Sets*](https://mathweb.ucsd.edu/~asuk/dilworth.pdf)

2. **What three neighbors force.** Repeatedly remove vertices of degree at most two. In the remaining graph, fix two left vertices. Every other left vertex has at least three right neighbors. Each of the two fixed vertices can block at most one of those neighbors, because sharing two would give a four-cycle. Thus the complement of every pair of left vertices is a union of right neighborhoods. Those complements are pairwise incomparable, so a core with `a` left vertices requires at least `choose(a,2)` factors. Restricting the original orderings to the remaining graph preserves exactness.

3. **Counting edges.** Each right vertex of degree `d ≥ 3` contributes `d` edges and accounts for `choose(d,2) ≥ d` distinct left pairs. No two right vertices account for the same pair. Hence the core has at most `choose(a,2)` edges and therefore at most as many edges as there are factors. Each vertex removed earlier accounts for at most two further edges.

4. **Counting gates when factors share work.** Let `v` be the number of original nonisolated vertices and `t` the number of distinct factor outputs needed after duplicates are removed. Every factor contains the original edges, so its output depends on all `v` inputs. A fan-in-two circuit needs at least `v−1` gates before it can produce the first factor. The other `t−1` distinct factor outputs each need a later gate. Thus `v ≤ s+1` and `v+t ≤ s+2`. If the core is empty the deletion count gives `e ≤ 2v`. Otherwise, with `v′ ≥ 1` vertices left, `e ≤ 2(v−v′)+t ≤ 2(s+1)`. The edgeless graph satisfies the claim directly.

The Lean development proves the prefix criterion, normalization of nested supergraphs, the pair counts, the deletion argument and the cost of producing distinct factor outputs in the project’s circuit model. The final theorem takes the bipartite incidence relation for counting and the edge functions realized at the selected circuit gates. In the application, each realized function is the corresponding supergraph on the original inputs. Containment of the original edges gives its required number of active inputs. The finite minimum counts above are checked by the Python certificates.

An algebraic expression may simplify before its factors ever appear on wires. A matching illustrates the distinction: its edge function is simply an OR of disjoint two-input ANDs, even though a representation by explicit chain factors may require many orderings. A general circuit that performs such simplifications lies outside the proved bound.

## Reproduction

Use the project’s pinned Lean 4.36.0 environment. Set `NOTES` to the absolute path of this research directory and run the following from the upstream repository’s `lean` directory. The first command creates a temporary directory for the compiled dependency. Both Lean sources stay in the notes directory. [Pinned project revision](https://github.com/open-goat/pequalnp-proofs/tree/056ae7099a75e637daeae581dfdbd0a4c3713d4a)

```sh
build_dir=$(mktemp -d)
lake env lean -R "$NOTES" -o "$build_dir/WitnessBound.olean" "$NOTES/WitnessBound.lean"
lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean "$2/ChainFactorBound.lean"' sh "$build_dir" "$NOTES"
python3 "$NOTES/chain_cover.py" --certificate "$build_dir/chain-certificate.json"
```

Independent research by helloitswill with AI assistance.
