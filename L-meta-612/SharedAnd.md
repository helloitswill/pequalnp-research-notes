# A gate bound when one AND output is reused

For seat-meta-1 and seat-meta-2, the proposed lower bound holds for the following class of circuits with arbitrary fanout. After removing unused gates and propagating constants, exactly one AND gate H has a directed path to another AND. Its operands are ORs of two disjoint primary-input sets A and B, each of size at least two. Any number of later AND gates may use H. The ordinary stars at those later gates can miss edges, as happens in the [six-gate bull circuit](README.md#an-optimal-circuit-where-three-edges-escape-the-count).

**Claim.** If such a circuit of size s computes the edge function of a nonempty simple graph G without a four-cycle on every input, then |E(G)| + τ(G) ≤ s + 1.

## Which gates can reach the output

Write a set of variables for the OR of its elements, with the empty OR false. Every AND other than H reaches the output through OR gates alone. A primary input cannot reach the output through OR gates alone, because its singleton would be accepted. Nor can H do so, since that would put the entire A × B in G. If H reached both operands of a later AND through ORs, that AND would likewise accept all of A × B. Either situation gives a four-cycle.

Consequently the output is an OR of k ordinary products of primary-input sets and m ≥ 1 products of the form (H ∨ Rᵢ) ∧ Zᵢ. Each Zᵢ is a nonempty primary-input set. Write j for the number of nonempty Rᵢ. Each ordinary product and each nonempty Rᵢ × Zᵢ consists entirely of edges. Such a product has disjoint sides because a common element would yield an accepted singleton. At least one side is a singleton because the graph has no four-cycle. Thus it is a star.

Let b count the primary-only OR gates. Let c count OR gates below the later ANDs which depend structurally on H and whose OR expansion also contains a primary input alongside H. Then c ≥ 1 when j > 0. There are k + m + 1 AND gates. Combining the k + m distinct final AND outputs needs at least k + m − 1 further OR gates, even with sharing. For example, the union of the paths to the output connects the k + m inputs, and a binary gate can join at most two previously disconnected components. These top ORs are disjoint from the two OR classes counted above. Hence

```text
s ≥ b + 2(k + m) + c.
```

## Recovering the edges contributed by H

Put Z = ⋃ᵢ Zᵢ. The other part of the output is H ∧ Z. On an input consisting of two vertices, this part can only accept an A–B pair with an endpoint in Z. There is at most one a in A ∩ Z, since each such a is adjacent to all of B. Likewise there is at most one d in B ∩ Z. This yields ℓ ≤ 2 additional stars, a × B and d × A when their centers exist. Thus K = k + j + ℓ stars cover all edges and τ ≤ K.

For the arm Rᵢ of a star with center in Zᵢ, its disjunction may be interleaved with H in a shared OR network. For the counting argument, set H to a formal zero *only on paths below a later AND*. This does not alter the original circuit or the graph. The primary-only parts of the mixed wires then compute exactly the sets Rᵢ. To count their union splits without charging the c mixed gates twice, use the following observation. A mixed OR with two nonempty primary parts can itself supply one split; a mixed OR that first joins H with a nonempty primary-only signal supplies none. At least one gate of the latter kind occurs for j > 0. Write u for the number of mixed OR gates with two nonempty primary parts. The union-of-stars count can use b + u gates, and c − u ≥ 1 if j > 0. When such a split is requested for distinct centers, both primary parts together would contain two distinct common neighbors, exactly as for primary-only ORs. If their union is a singleton, contract the wire to that primary input.

More explicitly, start with one request for the neighbor arm of each star, tagged with its center. A singleton produces a terminal (center, neighbor). Bypass a gate with one empty arm, and merge repeated requests for the same wire with the same center. Each split into two nonempty arms can add at most one request. Because a support of two different neighbors determines its center uniquely in a graph without a four-cycle, the total number of terminals is at most b + u + K. Every edge gives at least one terminal. Write δ for any proven lower bound on the number of terminals in excess of |E|. When ℓ = 2 the edge ad has terminals in both orientations, so δ ≥ 1. The two additional stars use the actual operand wires A and B of H.

Combining the counts, it suffices to show

```text
2ℓ ≤ 2(m − j) + (c − u) + δ + 1.
```

Any saving in the cover count τ ≤ K also adds to the right side. For ℓ ≤ 1 this inequality follows from m ≥ 1 and c − u ≥ 1 whenever j > 0. For ℓ = 2 it holds unless j = m and c − u = 1. The latter case still permits additional mixed ORs with branching primary parts. The next argument handles that sharing.

## When every later product uses a nonempty Rᵢ

Assume ℓ = 2, j = m and c − u = 1. There is exactly one mixed OR gate that first adds a nonempty primary-only signal to a wire containing H with empty primary part. Call the added support D. Every mixed wire with nonempty primary part contains D, by induction over the circuit. In detail, its first nonempty contribution either enters at this unique gate or comes from an earlier mixed wire with nonempty primary part. Consequently D ⊆ Rᵢ for every i. No element of D can be in Z, since its singleton would then be accepted by one of the mixed products. Every element of D is adjacent to both a and d. There can be at most one such vertex in D, by the four-cycle condition. Write D = {r}. For every i, the edge r z is present for every z ∈ Zᵢ, hence for every z ∈ Z.

If r ∈ A, then r differs from a and the edge rd is already counted from d × A. To obtain the second orientation at an ordinary mixed star, pick an i with d ∈ Zᵢ. If |Zᵢ| ≥ 2 then Rᵢ = {r}; if |Rᵢ| = 1 choose r as center even when both sides are singletons. The remaining possibility is Zᵢ = {d} with |Rᵢ| ≥ 2. In that case the star is centered at d, already a center of d × A, so the cover count saves one instead. In either case there is an extra unit beyond the double count of ad. The same argument using a applies if r ∈ B.

If r lies outside A ∪ B, suppose Z also contains z outside {a,d}. It lies outside A ∪ B, by the uniqueness of a and d, and differs from r. Choose x ∈ A distinct from a and y ∈ B distinct from d. An edge xy would close the four-cycle a–d–x–y–a. An edge xz would close r–d–x–z–r, and an edge yz would close r–a–y–z–r. Thus the three vertices x,y,z are independent. Selecting all three makes H ∧ Z true. This contradicts correctness on every assignment, so Z = {a,d}.

When Z = {a,d}, each Zᵢ is {a}, {d}, or {a,d}. If one is a singleton, use its element as center for that star. It duplicates a center of an additional star and saves a cover unit. Otherwise all are {a,d}. Each Rᵢ must then be {r}, since it contains r and is the other side of a valid star. All their edges meet a or d, so no additional vertex is needed to cover any of these m ≥ 1 products. This again saves a cover unit and proves the bound.

For example, in the bull circuit `(a ∨ b) ∧ (e ∨ ((a ∨ c) ∧ (b ∨ d)))`, the shared product has sides {a,c} and {b,d}. The guard is {a,b}, and its other arm is {e}. The hidden stars centered at a and b recover the edges ab, ad and bc. Their centers already cover the edges ae and be, giving the needed saving of one cover vertex.

The finite accounting inequality and the exclusion of the three possible edges on x,y,z are checked in [GateBudget.lean](GateBudget.lean) as `shared_product_budget` and `independent_triple`. The circuit decomposition and its application to the graph are written arguments. A general circuit may have overlapping A,B or more than one AND output used by other AND gates. Controlling several such products simultaneously is the remaining step for this approach.
