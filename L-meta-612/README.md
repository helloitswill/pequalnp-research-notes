# Counting gates for square-free graph edge functions

For the two project seats working on L-meta-612, seat-meta-1 and seat-meta-2.

The proposed minimum is attained on every graph with at most five vertices. Two consequences extend to graphs of arbitrary size. The bound holds if the graph has a vertex cover of size at most two. It also holds if the given circuit has at most two AND gates, even with unrestricted sharing of intermediate results. A six-gate circuit on the five-vertex bull graph rules out a natural shortcut for counting the gates of an optimal circuit.

These conclusions combine exact finite enumeration with the reductions below. Lean 4.36.0 checks the separate counting inequalities and Boolean identities in [GateBudget.lean](GateBudget.lean). The universal project statement remains open in this work.

## The target and the finite check

Write `F(G)` for the function that accepts a set of vertices exactly when the set contains an edge of the simple undirected graph G. Write τ for the minimum size of a vertex cover. The assignment asks whether every fan-in-two monotone circuit for `F(G)` has at least |E| + τ − 1 gates whenever G has an edge and no cycle of length four. An upper bound of this size follows by assigning every edge to an endpoint in a minimum cover, forming a star at each center, and taking the OR of the stars. Each center has an edge to a vertex outside the cover by minimality, so each center receives at least one edge.

The enumeration considers every labelled graph on five vertices, groups isomorphic graphs, and checks all potentially minimum circuits of up to eight gates. All 547 eligible labelled graphs, comprising 17 isomorphism classes, attain the claimed minimum. Isolated vertices include the smaller cases. An independent four-input program finds 53 eligible labelled graphs and the same minimum in every case.

Both searches compare truth tables on every input. In a minimum circuit for these nonconstant functions, propagate constants, eliminate unary gates and repeated operands, and discard unused gates. Invalid wire references in the project model read false and are covered by constant propagation. A gate equal on all inputs to a previous wire can be replaced by that wire. What remains is a list of binary gates on distinct earlier wires with distinct truth tables. A future gate can reduce the number of outstanding unused gate outputs by at most one. The five-input search also orders gates by nondecreasing depth and renames primary inputs in order of first use. Depth is invariant under input renaming. These choices retain a representative of every minimum circuit up to an input permutation.

## Reducing arbitrary graphs with a cover of size two

If two leaves have the same neighbor v, deleting one leaf x preserves τ. In the smaller graph a minimum cover may be chosen to contain v. If it omitted v, replacing the surviving leaf with v preserves coverage. The chosen cover also covers the deleted edge.

Fixing x to false in a circuit for the original graph removes at least one gate. Its value matters on an input selecting v and x, so some gate reads x on the way to the output. Each binary gate directly reading the fixed bit becomes either false or its other operand. Propagating constants and relabelling the surviving inputs gives a circuit for the smaller nonconstant function. Conversely, the proposed bound drops by one, since exactly one edge was deleted. Thus the lower bound lifts when the deleted leaf is restored. Isolated vertices can be removed by fixing their inputs to false.

Choose a cover of size at most two and perform these deletions. Any vertex outside the cover has all its neighbors in the cover. At most one private leaf remains for each cover vertex. If there are two cover vertices, at most one outside vertex is adjacent to both, since two common neighbors make a four-cycle. At most five vertices remain. The finite check therefore proves the lower bound for the original graph.

## Reducing arbitrary circuits with at most two AND gates

First propagate constants and discard unused gates. The output has no singleton on which it is true, so no primary input reaches it by OR gates alone. Before the first AND, each wire is a disjunction of primary inputs. Denote the output of the first AND by K = A ∧ B, where A and B are such disjunctions. At either input to the second AND, an OR circuit can contribute a disjunction of primary inputs and optionally K. Above the second AND, the output can also contain K as a disjunct.

If K reaches the output through ORs alone, its other appearances are absorbed. If K appears on both sides of the second AND, distributivity likewise makes it a separate disjunct. If K appears on neither side, the second AND is already a product of two disjunctions. In these cases the output is a union of at most two complete bipartite products. Their two sides must be disjoint, since a singleton cannot be an edge. Each nonempty product lies in G and is a star, since two vertices on each side make a four-cycle. The centers cover the graph.

The remaining output has the form T ∧ (S ∨ (A ∧ B)). Each capital letter denotes a disjunction of primary inputs. No variable in T can belong to S or to both A and B, since its singleton would then be accepted. Partition the primary variables as follows. Each letter in the table also denotes the OR of all variables in that class.

| Class | Membership |
| --- | --- |
| X | In T and A |
| Y | In T and B |
| Z | In T alone |
| C | Outside T and either in S or in both A and B |
| P | Outside T and C, in A only |
| Q | Outside T and C, in B only |

The remaining variables have no effect. If C is true, the inner expression S ∨ (A ∧ B) is already true. On C = false the inner product uses exactly X ∨ P and Y ∨ Q. Hence the output expands to

```text
CX ∨ CY ∨ CZ ∨ XY ∨ XQ ∨ YP ∨ ZPQ
```

Juxtaposition denotes AND. Lean checks the expansion for all values of the six class signals. If Z, P and Q all had representatives, selecting one member of each would be accepted, although each of its pairs would be rejected. Such a triple cannot occur for an edge function. At least one of those three classes is empty.

On two selected vertices, the possible edges are therefore exactly the six pair terms. On the classes they form a triangle C,X,Y with one possible private leaf at each corner, and at least one of the three leaf classes is absent. Each pair term gives every edge between its two classes. There are no edges within a class. Two vertices in the same nonisolated class have exactly the same neighbors. If they had two neighbors, those four vertices would form a four-cycle. Extra representatives are consequently duplicate leaves and can be deleted as above. One representative per nonempty nonisolated class leaves a subgraph of the triangle with at most two pendant leaves. Two triangle vertices cover this graph, and reversing the deletions preserves the cover number. This proves τ ≤ 2, giving the claimed gate bound by the preceding reduction.

## Counting edges exposed at AND gates

For a wire w, let L(w) be the primary inputs that can reach w by OR gates alone. For a primary input this is its singleton set. For an OR take the union of the two input sets, and for an AND use the empty set. Classify the gates that reach the output into p AND gates with two nonempty input sets, b OR gates with two nonempty input sets, and d other gates.

The first inequality is **p ≤ d + 1**. Scan backward from the requested output and keep distinct pending wires. Charge one unit for each pending wire whose set is empty. Visiting one of the p AND gates consumes a unit and adds none. A gate among the b ORs changes no units. Any other gate can add at most one net unit. In particular, a gate with two empty inputs also has an empty output. There is at most one unit initially. The Lean theorem `one_output` checks this accounting on a reverse gate list with duplicate requests removed, so a shared wire is visited once.

Select k of the p AND gates where the entire product L(left) × L(right) consists of graph edges. Each product is a star. Let H be the union of its edges over the selected gates. The second inequality is **|E(H)| ≤ b + k**. For the proof, choose a center for each of these k products. Trace the ORs that supply the other arm, labelling each request with the center. Contract any wire whose support consists of one input to that input, and bypass a wire whose only nonempty child has the same support. Every remaining split is a binary OR with two nonempty child supports whose union has at least two vertices. Such a physical gate can be requested by only one center. Two distinct centers would have those two inputs as common neighbors. Within one center, merge repeated requests for the same wire. Starting with k requests, each visited split can add at most one net request. Every covered edge gives at least one terminal (center, neighbor), and distinct edges cannot give the same terminal. Thus there are at least |E(H)| terminals and at most k + b. Lean checks the split count in `union_budget` and the common-neighbor argument in `unique_center`. The correspondence from the given circuit to this labelled list of ORs is a written argument.

Combining these inequalities gives |E(H)| + 2p ≤ size + k + 1. In particular, whenever H covers every edge, τ ≤ k ≤ p and the assigned lower bound follows. This argument allows other gates in the same circuit to reuse an AND output or to feed it into another AND.

## An optimal circuit where three edges escape the count

Take the bull with edges ab, ad, bc, ae, be. Its cover number is two, and its minimum is six by the enumeration. It has the following six-gate circuit.

```text
(a ∨ b) ∧ (e ∨ ((a ∨ c) ∧ (b ∨ d)))
```

The inner product includes the nonedge cd. The outer product exposes only ae and be by OR-only paths. Thus the proposed covering property can fail even in a minimum circuit. On four vertices every one of the 852 minimum ordered circuits enumerated had the covering property. On five vertices the bull was the sole isomorphism class with a minimum circuit missing an edge this way.

A different circuit with six gates computes the same function.

```text
(a ∧ ((b ∨ d) ∨ e)) ∨ (b ∧ (c ∨ e))
```

Lean checks `bull_rewrite` for arbitrary Boolean signals a,b,c,d,e. Exchanging an isolated copy of the gadget costs no additional gates. If intermediate gates have outside consumers, those consumers still need their signals. A proof for arbitrary circuits must account for such sharing or charge the hidden edges directly.

## Reproduction

Run from this directory with the project's Lean 4.36.0, Python 3.10 or newer, and a C++17 compiler.

```sh
elan run leanprover/lean4:v4.36.0 lean GateBudget.lean
python3 check_four.py
c++ -O3 -std=c++17 check_five.cpp -o /tmp/check_five
/tmp/check_five 8
```

The Lean check exits successfully. The Python program reports 53 labelled graphs and 852 optimal circuits. The C++ program reports 17 classes, 547 labelled graphs, zero classes below the bound, and one class with an optimal circuit missing an edge from the selected products. The project checker accepts only the exact universal statement. There is no proof submission for these partial results.

The standard single-level formulation appears in [Jukna, *Disproving the Single Level Conjecture*](https://epubs.siam.org/doi/10.1137/S0097539705447001). The project model and the earlier attempts are documented in the [circuit definitions](https://github.com/brilliant-hq/pequalnp-proofs/blob/main/lean/PEqualNP/Defs/CircuitLowerBounds.lean), the [withdrawal of PR 3055](https://github.com/brilliant-hq/pequalnp-proofs/pull/3055#issuecomment-7118762583) and the [checker verdict on PR 3178](https://github.com/brilliant-hq/pequalnp-proofs/pull/3178#issuecomment-7119823525).
