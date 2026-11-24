# A nonedge accepted by a gate owning two disjoint edges

In a graph without triangles or four-cycles, suppose a gate in a monotone fan-in-two circuit owns the disjoint edges `ab` and `cd`. Among the four pairs with one endpoint from each edge, some pair is a nonedge that turns the gate on. This gives an explicit input on which the gate fires although the graph's edge function is false.

An AND gate owns an edge when the gate is on at the input containing just its endpoints and all earlier AND gates feeding it, directly or indirectly, are off. The theorem `location_premise` proves the first premise of our proposed reduction for L-meta-1774 using the project's definition of ownership. Its wire and cone lemmas come from the project's checked L-meta-1762. [Lean proof](Tracing.lean) · [Upstream source](https://github.com/open-goat/pequalnp-proofs/blob/056ae7099a75e637daeae581dfdbd0a4c3713d4a/lean/PEqualNP/Outside/L_meta_1762.lean)

There is also a restriction that holds on every Boolean input. Either one of the four vertices alone forces the gate on, or one of the two expressions `(a OR c) AND (b OR d)` and `(a OR d) AND (b OR c)` forces it on whenever the expression is true. Every operand of a gate owning two disjoint pairs comes from an earlier OR gate. These statements use the wire-domination lemmas from the project's checked L-meta-1600. [Lean proof](OwnershipObstruction.lean) · [Upstream source](https://github.com/open-goat/pequalnp-proofs/blob/056ae7099a75e637daeae581dfdbd0a4c3713d4a/lean/PEqualNP/Outside/L_meta_1600.lean)

The remaining step is to use the accepted nonedge to change the circuit, preserve the function and size bound, and reduce the number of gates owning disjoint edges.

## Reproduce the checks

Use Lean 4.36.0 and checkout `056ae7099a75e637daeae581dfdbd0a4c3713d4a` of the upstream project. Run these commands from its `lean/` directory with the two proof files from this directory.

```sh
lake build +PEqualNP.Defs
lake env lean /path/to/Tracing.lean
lake env lean /path/to/OwnershipObstruction.lean
```
