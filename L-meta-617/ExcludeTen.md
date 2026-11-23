# L-meta-617 · Every monotone circuit for the cube edge function has at least eleven gates

Label the eight vertices by three-bit integers. Two vertices are adjacent when they differ in exactly one bit. The function is 1 when the selected vertices contain an edge. This is exactly the edge list in the assignment.

**Claim.** No monotone circuit in the recorded model with at most ten gates computes this function. The argument uses the project's checked six-cycle lower bound. The deduction for the cube below is a written proof.

### Simplifying circuits and fixing inputs

The project's [Monotone2 definition](https://github.com/brilliant-hq/pequalnp-proofs/blob/687a0753bb65edc3dae1e25dee238905156733dd/lean/PEqualNP/Defs/MetaComplexityLgpMono.lean) allows AND and OR gates of fan-in at most two. The [evaluation definition](https://github.com/brilliant-hq/pequalnp-proofs/blob/687a0753bb65edc3dae1e25dee238905156733dd/lean/PEqualNP/Defs/CircuitLowerBounds.lean) appends gates in order, reads a missing wire as false, and counts every gate once. For a nonconstant output we may normalize a circuit without increasing its size. Process the gates in order and represent each old wire by a Boolean constant, an input, or a wire of the normalized circuit. Missing operands denote false. Fold constants using the gate truth table, treat unary gates as aliases, and replace an AND or OR of a wire with itself by the same wire. Empty gates are constants. Append a gate only when two distinct nonconstant wires remain. Remap the output in the same way and discard any gates outside its dependency cone. The wire map preserves values by induction through the gate list. A nonconstant output needs no gate producing a constant.

The same construction after fixing one input to false eliminates every distinct gate that directly reads it. With an AND the result is false. With an OR the result is its other operand, possibly also false. This count includes all direct readers even if their other operands have already been simplified. Surviving input coordinates can be renumbered in any order by the wire map. When the output is nonconstant, no gate is needed to materialize constants.

### The cube has a multiply read input

Every cube vertex is essential. Selecting a single neighbor and then adding that vertex changes the output from 0 to 1. Thus the normalized cube circuit does not output a primary input and has a first gate. Its operands are distinct primary inputs, say vertices i and j. If every input had at most one direct reader, neither i nor j could occur again. This first gate is symmetric, so swapping just the assignments of i and j would leave the output invariant.

For every i and j the cube function distinguishes such a swap. There is a third vertex k adjacent to i and not to j: at Hamming distance one between i and j, flip a bit of i other than the differing bit; at distance two, flip the bit where i and j agree; at distance three, flip any bit. In these cases k has distance two, three, and two, respectively, from j. Selecting i and k gives an edge, whereas selecting j and k does not. This contradiction gives a vertex v with at least two distinct direct-read gates.

### Two restrictions leave a six-cycle

Set v to false. The simplified circuit loses at least two gates. Its function still depends on the antipodal vertex w, the bitwise complement of v. All three neighbors of w survive. Selecting one of them and then adding w changes the output. This residual function has other essential variables too, so the output cannot be w itself. At least one surviving gate must therefore directly read w; otherwise the circuit output would be independent of w. Setting w to false eliminates at least one further gate.

After these restrictions, renumber the six remaining primary inputs in cyclic order. Bitwise XOR by v sends the deleted pair to 0 and 7. With those two vertices removed, the cycle order is 1, 3, 2, 6, 4, 5. These six consecutive pairs, including the wraparound, are exactly the surviving cube edges. The resulting circuit computes the ordinary six-cycle edge function in this order and uses at most three fewer gates than the original circuit.

The project's [L106](https://github.com/brilliant-hq/pequalnp-proofs/blob/687a0753bb65edc3dae1e25dee238905156733dd/lean/PEqualNP/MetaComplexity/L106.lean) gives the exact size of the n-cycle for n at least five in the larger fan-in-two AND/OR/NOT model. It states that a size budget s is sufficient exactly when n + floor((n+1)/2) ≤ s+1. At n=6 this requires at least eight gates. A monotone circuit is also in that larger class, and renumbering or removing the two fixed inputs introduces no gates. Thus the original cube circuit has at least 2 + 1 + 8 = 11 gates.

This answers the assignment's mathematical question at its ten-gate threshold. It does not construct an eleven-gate circuit or establish the cube's exact complexity. The desk's Lean target asks for existence of a ten-gate witness; this written lower bound proves its negation. The project would need to post a matching lower-bound statement for a proof PR under its current rules.
