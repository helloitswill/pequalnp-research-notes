# Exact minima for cover size four and for graphs through eight vertices

For seat-meta-1 and seat-meta-2, a counterexample to L-meta-612 must have at least nine vertices and minimum vertex-cover size at least five. The graph must have an edge and contain no cycle of length four, including cycles with chords. Circuits may share arbitrary AND and OR outputs and must compute the edge function on every Boolean assignment.

The exact minimum in the two families is |E| + τ − 1. Choose one center per vertex of a minimum cover and assign each edge to one such endpoint. A star with d assigned edges costs d gates, and joining the τ stars costs τ − 1 more. For the lower bound the following reductions and exhaustive computations exclude every smaller circuit.

| Graphs checked | Remaining cases by number of vertices | Total |
| --- | --- | ---: |
| Cover size four, any number of vertices | 6 vertices: 2, 7: 13, 8: 19, 9: 7, 10: 3 | 44 |
| Through eight vertices, cover size four or five, after removing isolates and duplicate leaves | 6 vertices: 2, 7: 28, 8: 140 | 170 |

The rows overlap. Of the 140 eight-vertex cases in the second row, 118 have cover size four and 22 have cover size five.

## Reducing the graph lists

For an arbitrary graph with cover size four, first [remove isolates and duplicate leaves and enumerate the outside neighborhoods](CoverThree.md). This gives at most fourteen vertices. Apply the [three leaf reductions](LeafReductions.md) whenever possible. Each application reduces the vertex count and preserves the implication from the smaller graph's lower bound to the original bound. Enumerating the remaining graphs up to isomorphism gives the first row. Cover size at most three was checked separately. This proves the new result by induction on the number of vertices.

For the second row, every seven-vertex graph without a four-cycle has three independent vertices. Otherwise the nonneighbors of each vertex, excluding that vertex itself, form a clique of size at most three. Every degree is therefore at least three. The sum of the numbers of pairs of neighbors at each vertex is at least 7 · 3 = 21, and at most 21 because any pair has at most one common neighbor. Every vertex would have degree three, giving an odd total degree. This is impossible. On eight vertices, taking an induced seven-vertex subgraph gives an independent triple and hence a cover of size at most five. On six vertices a graph with no four-cycle has two nonadjacent vertices, and hence a cover of size at most four. Along with the previous cases, this exhausts the possible cover sizes.

An independent generation starts with one vertex and extends each graph by every possible neighborhood for the new vertex. It rejects an extension exactly when the new vertex would have two common neighbors with an old vertex. Up to isomorphism the nonempty graph counts for orders two through eight are 1, 3, 7, 17, 43, 116 and 350. Removing isolates, duplicate leaves and graphs with a three-vertex cover gives exactly the same 170 representatives. Isomorphism is tested by refining degree classes using the colors of adjacent vertices, trying every permutation inside the resulting classes, and retaining the least encoded adjacency matrix.

## Using exact bounds from smaller graphs

The [direct search](CoverThree.md#what-the-searches-exhaust) checks last-use schedules of binary circuits and compares them on the minimal positives and maximal negatives. The optional `--smaller-optimal` mode also uses a lower bound already proved for G − v. Its dependency is strictly on graphs with fewer vertices. Both families in the table are closed under deletion when the cases of smaller cover size are included.

Suppose the current budget is B. For a vertex v such that G − v has an edge, let Dᵥ = B − (|E(G − v)| + τ(G − v) − 1). Fixing v to false can remove at most Dᵥ gates from a correct circuit of size at most B. A wire that vanishes on this restriction is identifiable by evaluating it with every other input true. Monotonicity makes that evaluation exact. Every gate reading a vanishing wire can be removed by constant propagation. Counts for each v are maintained separately.

If q live wires vanish at v = false, at least q more gates must disappear before the output is reached. Each gate can reduce the number of these live wires by at most one. In particular, a gate reading two vanishing wires also vanishes. The output survives since G − v has an edge. In a last-use schedule for a circuit with all gates used, its output is the sole wire at completion. Thus the search may reject a state whenever the remaining deletion allowance minus q is negative.

This quantity initially equals Dᵥ − 1. When a binary gate consumes its two operand occurrences, it decreases by one exactly for AND with one vanishing and one surviving operand. Retaining a vanishing operand for a later consumer decreases it by one further unit, independently for each operand. The four Boolean possibilities give the identity `restriction_cost` in [GateBudget.lean](GateBudget.lean). Memoization includes these remaining allowances as well as the complete live wire values and the gate budget. The optional final argument selects the number of hash-table index bits. Hash collisions only evict entries and do not change the result.

The last ten-vertex case has fourteen edges and cover number four. Start with four vertices, put a distinct common neighbor on each of their six pairs, and add two disjoint edges among the original four vertices. The search excluded all circuits of at most sixteen gates and produced a seventeen-gate circuit. An independent truth-table evaluation checks all 1,024 assignments for that witness.

## Reproduction

Use Python 3.10 or newer, a C++17 compiler such as Clang or GCC, and the Lean version shown below. The first three runs reproduce the case lists. Each lower-bound run prints one `NONE` result per graph at budget |E| + τ − 2. The published [per-graph transcripts](SearchResults.txt) include the graph indices, budgets and verdicts. The `check_star.py` runs build the upper-bound circuit for every graph and evaluate it on every assignment.

```sh
python3 -B cover_four.py > /tmp/cover4.txt
python3 -B small_cases.py > /tmp/through8.txt
python3 -B verify_small_graphs.py
c++ -O3 -std=c++17 kernel_search.cpp -o /tmp/cover-search
/tmp/cover-search 0 43 0 --smaller-optimal < /tmp/cover4.txt
/tmp/cover-search 0 166 0 --smaller-optimal < /tmp/through8.txt
/tmp/cover-search 167 167 0 --smaller-optimal 18 < /tmp/through8.txt
/tmp/cover-search 168 168 0 --smaller-optimal 19 < /tmp/through8.txt
/tmp/cover-search 169 169 0 --direct 20 < /tmp/through8.txt
python3 -B check_star.py < /tmp/cover4.txt
python3 -B check_star.py < /tmp/through8.txt
elan run leanprover/lean4:v4.36.0 lean GateBudget.lean
```

To check the actual synthesis witness on the fourteen-edge graph, isolate the last row and add one gate to the search budget.

```sh
tail -n 1 /tmp/cover4.txt > /tmp/last-graph.txt
/tmp/cover-search 43 43 1 --smaller-optimal < /tmp/last-graph.txt > /tmp/last-witness.txt
python3 -B verify_controls.py --smaller-optimal /tmp/last-graph.txt /tmp/last-witness.txt
```

## What extending the bound would imply

For a prime p take the p² points (x,y) and the p² lines y = ax + b over the field of p elements, keeping all incidences. Two distinct points share at most one line, so the graph has no four-cycle. Each line contains p points, giving p³ edges. Matching the line (a,b) to (a,a² + b) is a bijection onto the points, so its cover number is exactly p². The unrestricted conjecture would give a minimum of p³ + p² − 1 gates on 2p² vertices. This would yield an explicit family with a lower bound of order n^{3/2}, of the type sought in Jukna's Problem 8.2. [Jukna, *Disproving the Single Level Conjecture*, section 8](https://web.vu.lt/mif/s.jukna/ftp/single1.pdf)
