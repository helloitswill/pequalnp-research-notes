# Searching for sparse circuits for high-girth edge functions

L-meta-2029 asks for graphs without triangles or four-cycles whose edge counts grow arbitrarily large relative to the size of a fan-in-two monotone circuit computing their edge functions. On a vertex subset the output must be true exactly when that subset contains an edge. The existence of the requested family remains open in this work. [Project assignment and contribution rules](https://pequalnp.com/join.txt)

## Second look at a construction

We tried representing the full edge function as an AND of ordered bipartite supergraph tests. For any fixed bipartition without four-cycles, a fan-in-two circuit that produces every factor on a wire and uses their conjunction has at most twice its gate count plus two original edges. On the order-three incidence example the construction requires exactly 36 factors, while the point-star circuit uses 35 gates in total. [Proof, certificates and reproduction](ChainFactors.md)

## How small can a counterexample be?

Let `v` count vertices incident to an edge, let `e` count edges and let `s` count circuit gates. The circuit needs to read each of those vertices. Rewinding a gate in the output's dependency set replaces at most one demanded wire by two inputs, giving `v ≤ s+1`. At any vertex, two distinct branches of length at most two cannot meet again without making a triangle or four-cycle. Counting these branches and using Cauchy–Schwarz gives `4e² ≤ v²(v−1)`. The graph inequality is the girth-five case of the Moore bound. The Lean proof derives it directly with isolated vertices excluded. [Alon, Hoory and Linial](https://web.math.princeton.edu/~nalon/PDFS/ahl1.pdf)

For any positive integer `c`, beating that factor means `e > c(s+1)`. A witness must have **at least `4c²+4` nonisolated vertices, at least `4c²+4` gates, and a vertex of degree greater than `2c`**. For example, at `c=10` it needs at least 404 nonisolated vertices and 404 gates. The degree condition rules out taking arbitrarily many disjoint copies of a fixed graph, even with a fresh circuit designed for the whole union. [Lean proof, including `positive_witness_threshold`](WitnessBound.lean)

The extra two vertices and three gates over the direct estimate come from excluding equality in `v ≤ s+1`. In a violating graph the edge count exceeds the number of nonisolated vertices, so the graph contains a cycle. Four successive vertices on that cycle induce a four-vertex path. If `v=s+1`, every relevant binary gate must introduce two distinct, previously undemanded input wires when rewound. The resulting restriction to the path would be a formula in which each variable occurs at most once. A finite check over root partitions, with a separate induction for constant branches, proves that no such formula computes the path’s edge function. Thus `v ≤ s`. Substituting the strict integer inequality `e ≥ c(v+1)+1` into the graph bound yields the stated threshold.

[ProductObstruction.lean](ProductObstruction.lean) verifies that a Cartesian product has a four-cycle whenever both factors have an edge. For a direct product it suffices for each factor to have a vertex with two distinct neighbors. Jukna's small-circuit construction for saturated graphs adds cliques on each shore. Keeping three vertices of either clique already violates the girth hypothesis. [Jukna, Theorem 2.1](https://web.vu.lt/mif/s.jukna/ftp/single1.pdf)

## Exact tests for circuit search

The benchmark uses points `(x,y)` and lines `y=ax+b` over the fields of orders two and three, excluding vertical lines. A positive test selects the two ends of an edge. A negative test selects a maximal independent set. Every positive input contains a positive test, and every negative input is contained in a negative test. A monotone circuit passing these tests therefore computes the full edge function. Flipping any one boundary value yields another monotone function, so every row is necessary when a fixed test suite must distinguish the target from *all* monotone functions. An assumed gate budget or access to an implementation can give further information. [Lean proof](BoundaryTests.lean)

| Field order | Vertices | Edges | Girth | All inputs | Edge tests | Maximal independent sets | Exact test rows | Gates in star circuit |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 8 | 8 | 8 | 256 | 8 | 10 | 18 | 11 |
| 3 | 18 | 27 | 6 | 262,144 | 27 | 110 | 137 | 35 |

The star circuit first takes the OR of all lines incident to each point, then tests the point and takes the OR over points. A second circuit in the benchmark tests adjacency correctly whenever exactly one point and one line are selected. At order three it nonetheless accepts 1,521 independent subsets. For instance it accepts the point `(0,0)` together with the horizontal lines `y=1` and `y=2`.

CaDiCaL 2.1.2 recovered the prescribed 11-gate and 35-gate star circuits, and both decoded circuits passed exhaustive verification. Searches for a 10-gate circuit at order two and a 34-gate circuit at order three reached their time limits. Those runs give no lower bound at either budget. The encoder uses binary gates, permits repeated operands, and fixes the last gate as output. Constant folding removes constants and unary gates from a circuit computing this nonconstant function, and copy gates can pad any smaller circuit to the requested positive budget.

## Reproduction

Use the proof repository at revision `056ae7099a75e637daeae581dfdbd0a4c3713d4a` with its pinned Lean 4.36.0 environment. With the project dependencies built, set `NOTES` to the absolute path of this directory and run the Lean commands from the project's `lean` directory. The Python commands run from this notes directory. [Pinned project source](https://github.com/open-goat/pequalnp-proofs/tree/056ae7099a75e637daeae581dfdbd0a4c3713d4a)

```sh
lake env lean "$NOTES/WitnessBound.lean"
lake env lean "$NOTES/BoundaryTests.lean"
lake env lean "$NOTES/ProductObstruction.lean"
```

```sh
python3 affine_benchmark.py
python3 affine_benchmark.py --q 3 --write-tests rows.json
python3 synthesize.py --q 3 --gates 35 --pin-star --solver cadical
python3 synthesize.py --q 3 --gates 34 --seconds 120 --output candidate.json
```

For the researcher searching L-meta-2029, a candidate circuit can be passed to `affine_benchmark.py --q 3 --circuit candidate.json`. A construction for arbitrarily large orders still needs a bound on circuit size and a correctness proof for every vertex subset.

Prepared by helloitswill with AI assistance as independent research for L-meta-2029.
