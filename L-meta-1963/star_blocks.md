# Exact costs for blocks of up to four stars

Take any two, three or four distinct point centers of the order-three plane and all four edges of each center. The same result holds for any choice of line centers. Consider a circuit that must accept the two-vertex assignment of every chosen edge and reject the 234 quadrangle assignments in L-meta-1963. Its minimum size is 9, 14 or 19 gates, respectively. It may read any of the 26 inputs, share wires freely and accept other untested assignments. The usual OR of the chosen stars attains these sizes.

Consequently a change confined to any such block of the 64-gate star construction cannot produce a 63-gate circuit. The rest of the star terms can be held fixed at the output OR. On each chosen positive edge all the other stars evaluate to false, so the replacement must itself accept that edge. On each prescribed negative it must reject. Reusing an intermediate gate already paid for by the remainder would change this cost model and is an open possibility.

## Reduction to small instances

Set to false every input outside the selected stars. On negative rows use the projection to the remaining inputs. The projection is coordinatewise below the original negative row, so every fitting monotone circuit rejects it. On each selected edge the assignment is unchanged. Keep the inclusion-maximal projected negatives since they collectively force all the others to be false.

If a leaf is the neighbor of just one selected center, fixing that leaf to false saves at least one gate. The edge with its center is required true while the center singleton is required false by monotonicity from a quadrangle negative. Thus the leaf is essential before deletion. It cannot be the output since a singleton true at that leaf is also forbidden. At its first occurrence an AND becomes false or an OR copies its other operand. Constant propagation removes that gate. The same argument applies successively to the chosen private leaves because their edge assignments and both singleton restrictions survive the earlier deletions.

Keep all leaves shared by two or more selected centers. If all centers share just one leaf, keep a private leaf on each of the first two centers for blocks of size two or three, or on each of the first three centers for size four. For all other blocks remove every private leaf. The verifier enumerates the labeled center choices in both orientations and computes each residual minimum using the actual projected quadrangle negatives.

| Number of blocks | Centers per block | Private leaves removed | Residual minimum | Full block minimum |
| ---: | ---: | ---: | ---: | ---: |
| 156 | 2 | 4 | 5 | 9 |
| 104 | 3 | 7 | 7 | 14 |
| 468 | 3 | 6 | 8 | 14 |
| 26 | 4 | 9 | 10 | 19 |
| 936 | 4 | 7 | 12 | 19 |
| 468 | 4 | 4 | 15 | 19 |

## Checking the residual minima

For any residual graph, a minimum vertex cover of size t gives an upper bound of E + t − 1 gates, where E is the number of remaining edges. Assign each edge to a cover endpoint and join the resulting star terms. Every selected center receives an edge because the cover is minimal. Each of the n remaining inputs is essential by the preceding edge and singleton tests. A circuit that depends on n inputs needs at least n − 1 binary gates, by counting the edges in the connected subgraph feeding the output. The verifier also computes the lower bound for each restriction obtained by setting one vertex to false and discarding vertices that then have no edge. Any fitting circuit costs at least one more gate than each such lower bound. An empty edge set contributes the trivial lower bound zero.

When these estimates leave a gap, search the binary AND/OR gates in evaluation order. Each step chooses two live wires, either gate operation and which operands remain for later use. All inputs must be used, and every gate of a smallest circuit feeds the output. Hence some last-use schedule of every smallest circuit is covered. A gate can reduce the number of live wires by at most one. Nullary gates, unary gates and repeated operands can be folded or removed, as can wires constant or duplicate on all the specified examples. An invalid output is false and fails the edge tests.

A pair consisting of a positive and a negative row must be distinguished by a live wire true on the former and false on the latter. Once this condition fails no subsequent monotone gate can restore it. Wire values on all test rows distinguish memoized states. When restriction bounds are used, include the all-true assignment with vertex v omitted for every v. The graph in each such search has an edge avoiding v, so its required output on this assignment is true. A wire false on this assignment vanishes identically after setting v to false.

For each vertex, let its allowance be the trial gate budget minus the lower bound for its restriction. Every gate with a vanishing operand can be removed upon restriction. At a search state with z live vanishing wires at least z more such gates must be used as the output survives, and one gate can reduce the live vanishing count by at most one. The remaining allowance minus z is therefore nonnegative. It starts at allowance minus one. When both operands retire, the quantity drops by one precisely for an AND with one vanishing operand, as follows by testing the two operand values. Retaining either vanishing operand decreases the quantity by one more. The verifier uses these updates to prune the search.

Run from the folder containing this note with Python 3.10 or later.

```sh
python3 -B star_blocks.py
```

This is an exhaustive finite computation with a written reduction. The global strict-compression claim in L-meta-1963 remains open.
