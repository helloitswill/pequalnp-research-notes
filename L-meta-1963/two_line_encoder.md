# A 39-gate lower bound with at most two affected line outputs

Consider a binary AND/OR circuit on the thirteen point inputs of the plane of order three. For each of the thirteen lines, a designated output must be true on precisely its four incident point singletons. A wire's signature is the set of point singletons where it is true. On these signatures, AND computes intersection and OR computes union.

If at least eleven line outputs have OR-only cones, the full encoder needs at least 39 gates. This includes encoders with at most two AND gates whose signatures contain two or more points. The bound is sharp since three binary ORs per line suffice.

## Reserving the pure gates

In an OR-only cone every wire contributing to an output has signature contained in the output's line. At least three gates with signatures of size at least two are needed for that cone. To see this, allow all singleton and empty signatures for free. A union making all four points requires three binary gates even with arbitrary reuse: its output cone depends on four distinct free singleton leaves and a binary cone with g internal gates has at most g + 1 distinct leaves. Distinct lines intersect in one point, so a gate with at least two points in its signature can belong to at most one such cone. Reserve at least 33 distinct gates in eleven pure cones.

Let A and B be the other two lines. Restrict attention to their seven point singletons. Write c for the common point, with a₁,a₂,a₃ and b₁,b₂,b₃ the two sets of private points. Each of the other lines meets A ∪ B in just c or in a pair aᵢ,bⱼ. Thus every reserved gate projects to the empty mask, one singleton, or one of these nine cross-pairs. All these masks and the entire seven-point mask may be granted for free. Substituting free wires for the selected gate outputs leaves a legal straight-line program on the seven rows; this substitution also works when the original gates were shared.

## Six additional gates

Neither target A nor B is free. A putative five-gate program reaching both uses at most three gates whose values differ from both targets. Repeated values may be reused at no cost. The verifier keeps the set of distinct nontarget intermediates built so far. At each state, it introduces any target that can already be produced as a binary operation, charging that target one of the two reserved target steps. It repeats until no further target can be introduced. Introducing a producible target earlier preserves every later use of that wire. It then tries every binary union and intersection of currently available masks as the next nontarget gate. A repeated operand copies its input and the two nullary constants are already free. The state set includes every legal order, including those that reuse one completed target in producing the other.

The run visits 1, 48, 1,386 and 30,391 states at successive nontarget depths. No state reaches both targets. Three OR gates for each line give a six-gate construction, proving exactness for this relaxed problem. Together with the 33 reserved gates this proves the encoder bound.

## Counting AND gates

On singleton inputs a gate with empty signature can be treated as constant false and folded through later gates. A gate with singleton signature can be replaced by that point's primary wire. No extra gate is needed for a flat empty output, since each required output has size four. These reductions preserve all the stated output tests. In the resulting circuit, for any output still depending on an AND, take a last AND on a path to that output. Its signature has at least two points and survives through the OR gates after it. The same AND cannot be last for two different line outputs: its signature would be contained in two lines meeting in only one point. Thus at most two AND gates with signatures of size at least two imply at most two affected outputs. The other eleven have pure cones as above.

Run the standalone check with Python 3.10 or newer.

```sh
python3 -I -B two_line_encoder.py
```

The check includes all 78 choices of the two lines. This argument concerns a thirteen-output point encoder on singleton inputs. It does not by itself settle the global strict-compression task.
