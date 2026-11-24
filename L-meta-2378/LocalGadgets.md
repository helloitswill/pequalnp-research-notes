# Local OR-gate savings

Let a patch circuit use `k` binary OR gates, arbitrarily many binary AND gates, and a subset of the 42 input variables. Suppose it rejects every independent input there and accepts `a` distinct point–line incidences on two-variable inputs. Add one AND per uncovered incidence and join these additional terms to the patch output with ORs. The full edge function then uses `k+105−a` ORs. Solving L-meta-2378 by this construction requires `a ≥ k+2`.

**No patch on at most nine variables achieves this saving.** The local claim also allows accepting any larger vertex set that contains a genuine incidence. The exact unrestricted 42-input question remains open in these calculations.

## Removing leaves

Consider the graph whose edges are the accepted incidence pairs. Setting a variable of degree zero to false preserves the accepted pairs. If a vertex of degree one is incident to an accepted pair, its variable affects the output: its pair is accepted and the singleton at the other endpoint is rejected. There is a path of gates from that input to the output. When another accepted pair survives, no such path can consist entirely of ANDs, since setting this variable to false would then force the output to false. On the path up to its first OR, setting the variable to false zeros that OR's input. Its output can be replaced by the other operand. This removes one accepted edge and at least one OR. Iteration preserves a saving until the accepted-pair graph has minimum degree two. Having at least two more accepted pairs than OR gates rules out termination at zero or one edge.

The positive incidence graph is bipartite, and a pair of vertices on one shore has at most one common neighbor. In a core with shore sizes `l ≤ r`, each right vertex consumes at least one of the `choose(l,2)` distinct left pairs, so `r ≤ choose(l,2)`. For a core on at most nine vertices the only possibilities are:

* With three vertices on the smaller shore, there are three on each side, and the pair count forces a six-cycle.
* With four on each side, the right-neighborhood sizes are either all two, or three, two, two, two. In the first case both shores have degree two and form an eight-cycle. In the second, the three size-two columns must be the three pairs joining the leftover point to the points in the triple. This is the theta graph of three internally disjoint paths of lengths 3, 3, 3.
* With four and five, all five right neighborhoods must have size two. They are five distinct pairs from a four-point set, so the graph is a subdivided complete four-vertex graph with one subdivided edge removed. Its three paths have lengths 2, 4, 4.

The ambient graph restricted to these core vertices has no further incidences. Adding a chord to a six- or eight-cycle on the same bipartition gives a four-cycle. The three-path cores already use the maximum edge count on their shore sizes. Consequently any sound output accepting all core edges computes its entire edge function, by monotonicity.

## All chordless cycles, by a written argument

For the edge function of the chordless cycle on `n ≥ 5` vertices, the minimum number of binary OR gates is **exactly `n−1`**, with arbitrarily many binary AND gates allowed. Taking the OR of the `n` edge terms gives the upper bound.

Flatten every AND-only region: each numbered OR has two inputs, each a conjunction of raw variables and earlier OR outputs. The final output is another such conjunction. This representation does not increase the OR count. Constant folding deletes redundant constant wires. If an arm contains more than two different raw variables, replacing it by false preserves acceptance of every edge pair and cannot introduce a positive on an independent set. The normalized function consequently still computes the whole edge function, by monotonicity. We can use this normalization throughout.

The leaf-removal argument above gives OR minimum `m−1` for a forest with `m ≥ 1` edges. Each removal saves an OR until only one edge remains.

Suppose a cycle circuit has at most `n−2` OR gates. Fixing any variable `x` to false leaves a path with `n−2` edges, requiring `n−3` OR gates. Each numbered OR with raw `x` present in either of its two conjunctions can be removed on that restriction. Consequently raw `x` occurs at at most one numbered OR gate. It cannot occur in the final conjunction because there is an accepted edge avoiding `x`.

Choose a minimum circuit satisfying the normalization and take its first OR, with output `h`. Its inputs are raw conjunctions. The set `S` of their variables has size at most four. It must contain at least two distinct variables, since a monotone function of at most one variable is a constant or a projection and could replace the first gate. Thus `S` is a proper subset of the cycle. Every member of `S` occurs at this gate and nowhere else as a raw input. The remainder computes a function of the single bit `h` and the variables outside `S`.

Connectedness supplies an edge from a vertex `u ∈ S` to a vertex `w` outside. Selecting `w` alone is rejected and selecting `u,w` is accepted, so `h(∅)=0` and `h({u})=1`. When no outside variable is selected, the output is false at both bit values: the empty selection and the singleton `u` realize those values. Hence there is no edge inside `S`. Every vertex of `S` has an outside neighbor and induces the same singleton bit value 1. The remaining circuit therefore assigns them identical neighborhoods outside `S`. Two different vertices of a chordless cycle of length at least five never have identical neighborhoods. This contradiction proves the bound.

The same proof applies to a sound patch accepting every cycle edge when the ambient graph restricted to the cycle vertices contains exactly those edges. For a bipartite incidence graph without four-cycles, every six-cycle and eight-cycle meets this condition. Longer cycles may have additional ambient edges, so a patch with those additional edges as permitted false positives requires separate analysis.

## Certificate

[local_or_search.py](local_or_search.py) searches the exact circuit model with unlimited AND gates. The two operands of each numbered OR, and the final output, are arbitrary conjunctions of inputs and earlier numbered ORs. This represents every original circuit by unfolding its AND-only parts. Conversely the conjunctions can be implemented with binary AND gates. Constant terms can be folded away from a nonconstant output. On each accepted edge we require a witness of truth. On each maximal independent set we require a witness of falsity. Monotonicity extends the tests to all vertex sets. Optional mode `--cover` only requires the specified number of accepted pairs.

A conjunction with a nonedge or more than two raw inputs never helps on a positive pair and may be set to false. Exchanging operands of an OR preserves the computed function. With `--sym`, the first useful OR can be taken from one representative of each graph-automorphism orbit. Its two raw terms have incomparable sets of true edge rows, since a dominated term could be dropped without losing edge coverage. Later adjacent independent gates can be topologically ordered by their edge truth vectors. Unneeded OR slots can be padded after a useful gate.

With `--peel-bounds`, setting an input to false removes every numbered OR with that raw input present in either operand. When the retained graph is a forest, repeatedly removing leaves down to a final edge shows that its exact OR minimum is its edge count minus one. This formula also holds when its only cyclic component consists of a previously certified six- or eight-cycle with trees attached. The option uses precisely those restriction bounds, so the cycle cases are checked first.

| Core | Edges | Excluded OR budget | Achieved by the OR of edge terms |
| --- | ---: | ---: | ---: |
| Cycle of length 6 | 6 | 4 | 5 |
| Cycle of length 8 | 8 | 6 | 7 |
| Theta with lengths 3, 3, 3 | 9 | 7 | 8 |
| Theta with lengths 2, 4, 4 | 10 | 8 | 9 |

With CaDiCaL 2.1.2 and standard Python 3, each command writes its DIMACS input and textual LRAT proof and independently checks each unit-propagation hint through the final empty clause. Wall-clock limits can be increased on slower machines. The positive control decodes the circuit and evaluates every Boolean assignment.

```sh
python3 local_or_search.py c6 4 --proof certificates/c6.lrat
python3 local_or_search.py c8 6 --sym --proof certificates/c8.lrat
python3 local_or_search.py theta333 7 --sym --peel-bounds --seconds 300 --proof certificates/theta333.lrat
python3 local_or_search.py theta244 8 --sym --peel-bounds --seconds 600 --proof certificates/theta244.lrat
python3 local_or_search.py K23 3 --candidate control.json
```

## Certificate fingerprints

These SHA-256 values identify the DIMACS and textual LRAT files used for the independent replay. The traces total several hundred megabytes and can be regenerated locally.

| Core | DIMACS SHA-256 | LRAT SHA-256 | Replayed derivations |
| --- | --- | --- | ---: |
| C6 | `653daede7affc3b550c38d87b52579b6d8a8706df36e72e3b05d49683ecab949` | `3421ed3783bd5bbb38dac1616838e1f9abdbc9a9420f7a7fa69d5f8c95a6998c` | 10,078 |
| C8 | `f6866151f1dcdba8c23024814282098ef47e470583c420a8b64894eebf676094` | `09e81ae0cb1f06043c01c0f645bcf644aa85276a9e9189cf48808fbd0b90ea54` | 102,765 |
| Theta 3,3,3 | `bdd53b4b41ea0ce3c200f9e97fbf7b3056b6fa69038d3ed1ed194e707b9c6792` | `be2665d6aae7334013b489db850580546ae3b962fd7280b89fd826ef6e657360` | 153,651 |
| Theta 2,4,4 | `e25b74e9899882afe70ceb4fe8820121277dfd34c977d329c7adfdbd9c8b4892` | `a69ba8a36db9b6e65e943288b9b49a5d5092ed0a823e263ba9cd722dbeb0a8e8` | 717,894 |
