# A 38-gate point encoder needs a nested AND

Consider the proposed 63-gate circuit that retains thirteen line ANDs and the twelve ORs that join their outputs. Its remaining 38 gates read only point inputs. A point output for line $L$ must accept the singleton of each point on $L$. It must reject every quadrangle disjoint from $L$, because the corresponding negative row activates the line input for $L$.

**If no point-side AND feeds another point-side AND, directly or through other gates, the encoder needs at least 39 OR gates.** Three binary ORs per line attain the bound. The result allows arbitrary reuse of point wires and any number of AND gates in parallel. A separate bound excludes every encoder of at most 38 gates that has at most two ANDs, including nested ones. It uses only the singleton tests. [Earlier two-line bound](two_line_encoder.md)

## What a smaller encoder would have to do

Call a wire safe for $L$ if it rejects all quadrangles disjoint from $L$. Its singleton signature is the set of points whose individual inputs make it true. A safe wire has signature contained in $L$. Every point outside $L$ lies in a quadrangle disjoint from $L$, so accepting that singleton would also accept the quadrangle by monotonicity.

With fewer than 39 OR gates, some line must have a safe AND gate with at least two points in its singleton signature whose **two operands each accept an exterior quadrangle**. The quadrangles accepted by the two operands are necessarily different. At least one of those operands accepts an exterior quadrangle while rejecting every individual point of that quadrangle. An OR of raw point inputs cannot do that. That operand therefore has another AND in its ancestry. A circuit search can test this condition by evaluating the wires on the thirteen singletons and 234 quadrangles. [Lean theorem and encoder semantics](PointEncoder.lean)

## The 156 collinear triples

Any encoder with at most **38 gates in total**, even with arbitrarily nested ANDs, must accept a specific kind of extra input. For some ordered pair of distinct lines $L,M$, the output for $L$ must be true when the three points of $M$ outside $L$ are the only selected points. There are 156 candidate evaluations. A synthesis search can require that at least one of these evaluations be true. These are extra inputs beyond the project's 286 required rows. [Lean theorem for the project's circuit type](ExteriorTriple.lean)

For each $L$, there are nine points outside it and 84 ways to select three. Twelve of these triples are collinear, one for each other line. Each of the remaining 72 triples lies in three quadrangles disjoint from $L$. Acceptance of any such triple would force acceptance of a prescribed negative by monotonicity. A circuit rejecting all 156 collinear cases would therefore reject every set of at most three outside points at every line output. The project's checked multi-output bound then applies with $k=3$ and a charge of three per line. Thirteen lines give a lower bound of 39 total gates. Lean verifies the specialization and the finite covering argument. The general counting theorem is due to k-sandhu and was already checked upstream. [Existing proof L-meta-782](https://github.com/open-goat/pequalnp-proofs/blob/056ae7099a75e637daeae581dfdbd0a4c3713d4a/lean/PEqualNP/Outside/L_meta_782.lean)

## Why three ORs are needed per line

Fix $L$ and suppose every safe AND with two or more positive singletons has a safe operand. Start with its four points in four separate groups. Process the wires in order. Maintain the condition that the singleton signature of every processed safe wire lies in one group, with the empty signature allowed.

An input wire satisfies this condition. A safe AND with two or more positive singletons inherits the condition from its safe operand because its signature is contained in that operand's. A safe OR has two safe operands. If their nonempty signatures lie in different groups, join the two groups and charge that OR. The line output accepts all four singletons, so at least three ORs must have been charged. Each charged OR has two distinct positive singletons on $L$ and no positive singleton outside $L$. Two different lines intersect at only one point. They cannot charge the same OR.

Lean checks the count by an equivalent argument using the first safe wire to reach four positive singletons. If an earlier safe wire already reaches three, at least two ORs have already occurred. Otherwise the two input signatures of the first four-point wire each have two points. The first safe OR carrying one pair must differ from the first carrying the other, since an earlier wire carrying both would already have four points. The four-point wire supplies the third OR. Summing the disjoint sets of ORs over the thirteen lines gives 39. [Counting proof](EncoderCount.lean)

## Why an earlier AND is necessary

Let $u$ and $v$ be the operands of a safe AND. If $u$ accepts a singleton $a$ outside $L$ and $v$ accepts a singleton $b$ outside $L$, some quadrangle disjoint from $L$ contains both. This also holds when $a=b$. Both operands would accept this quadrangle. Thus at least one operand rejects every singleton outside $L$. If that operand nevertheless accepts an exterior quadrangle, no point of the quadrangle can be a singleton witness for it. [Lean proof against the project's plane](EncoderOperands.lean)

There are 54 exterior quadrangles for each line. Every distinct pair of outside points belongs to exactly nine of them. One example explains why the argument has to allow a nested AND. Write $s$ for the OR of the four points on $L$, and take the three points $a,b,c$ outside $L$ on any second line. The operands $s \lor (a \land b)$ and $s \lor c$ each accept an exterior quadrangle. Their AND rejects every such quadrangle because a quadrangle cannot contain three collinear points. The verifier checks all 468 line-and-pair choices and all 156 ordered choices of two distinct lines. [Finite check](feature_geometry.py)

The global problem also allows mixed gates to share intermediate results in other ways. The theorem here applies to a separate point encoder with a designated output for each line. A 38-gate encoder with the nested configuration above is still open.

## Reproduction

Use Lean 4.36.0 in the upstream proof repository at commit `056ae7099a75e637daeae581dfdbd0a4c3713d4a`. From its `lean` directory, set `notes` to the absolute path of this research folder and run the following commands.

```sh
lake build PEqualNP.Defs PEqualNP.Outside.L_meta_782 PEqualNP.MetaComplexity.Helpers.LowMergeWires
out=$(mktemp -d)
lake env sh -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  for name in PlaneTests EncoderCount EncoderOperands PointEncoder ExteriorTriple
  do
    lean -R "$2" -o "$1/$name.olean" "$2/$name.lean" || exit 1
  done
' sh "$out" "$notes"
python3 -I -B "$notes/feature_geometry.py"
```
