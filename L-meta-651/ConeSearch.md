# Local replacements using NOT in the 20-gate Petersen circuit

We checked all 454 connected single-output tree subcircuits containing between two and eight gates in the project's 20-gate circuit. Replacing any one of them by a smaller circuit on its boundary wires, with at least one unary NOT leading to the replacement output, cannot compute the Petersen edge function. The check allows shared gates inside the replacement and takes account of inputs on which the rest of the circuit hides a change. The lower bound for arbitrary 19-gate circuits remains open.

The reference circuit is the gate list in the project's [L-meta-587 proof](https://github.com/brilliant-hq/pequalnp-proofs/blob/3ec921591ffc6536fad46069ec0c219464fb6ffc/lean/PEqualNP/Outside/L_meta_587.lean). Wires 0 through 9 are primary inputs and the first gate produces wire 10. The checker independently builds the truth table from the fifteen graph edges and verifies the gate list on all 1,024 assignments.

## What was searched

A **cone** starts at one gate, its root. We can grow it backwards by taking a gate that supplies a boundary wire if its output has just one use and that use is inside the cone. This enumerates the connected tree cones whose interior gates have no external uses. A replacement may read any of the wires entering that cone. All other original gates and their connections are fixed. Simultaneous edits to separate cones and replacements that read other wires lie outside this search.

Suppose a candidate replacement of a $k$-gate cone contains $g\le k-1$ gates after unused gates are removed. At least one gate must be a live unary NOT. If there are $h\ge1$ such gates, the number of incoming gate connections is at most $2g-h$. To connect the $g$ gates and $s$ distinct input signals to one output requires at least $g+s-1$ connections. Thus $s\le g-h+1\le k-1$. A constant or a passthrough does not enlarge the set of variable signals the replacement can use.

For each root we separately force its value to 0 and to 1, then recompute the full circuit. The input rows on which those output values differ are the **care rows**. On each such row, the target truth table fixes the value the replacement must produce. For a chosen subset of boundary wires, group the care rows by their values on exactly those wires. If one group requires both output values, even an arbitrary Boolean function on that subset cannot work. We need to test only subsets of size $\min(k-1,\text{number of boundary wires})$. Every smaller set is contained in a tested set and conflicting rows stay conflicting when a wire is removed.

| Gates in cone | Cones | Boundary subsets tested | Subsets with consistent labels | Subsets surviving both tests |
|---:|---:|---:|---:|---:|
| 2 | 19 | 57 | 0 | 0 |
| 3 | 22 | 132 | 0 | 0 |
| 4 | 31 | 310 | 0 | 0 |
| 5 | 47 | 685 | 0 | 0 |
| 6 | 72 | 1,452 | 0 | 0 |
| 7 | 108 | 2,835 | 0 | 0 |
| 8 | 155 | 4,845 | 1 | 0 |
| **Total** | **454** | **10,316** | **1** | **0** |

## The last subset

The only consistent subset is for the eight-gate cone with wires 11, 14, 16, 17, 21, 23, 26, and 27. All seven of its boundary wires exhibit a forced positive change. In each row pair below, the indicated boundary wire changes from 0 to 1. The other six boundary values agree, and the required replacement output rises from 0 to 1. Row numbers encode the true primary inputs by their binary positions, with input 0 in the least significant position.

| Boundary wire | Row with wire 0 | Row with wire 1 |
|---:|---:|---:|
| 0 | 514 | 515 |
| 1 | 513 | 515 |
| 2 | 514 | 518 |
| 5 | 513 | 545 |
| 8 | 520 | 776 |
| 10 | 516 | 148 |
| 13 | 768 | 336 |

Any replacement for this subset needs all seven inputs. A candidate with at most seven gates and a live NOT must attain equality throughout the connection count. It has six binary gates and exactly one NOT. Its live wiring is a tree, with each of the seven inputs occurring once. At least one input lies below its NOT. As that input increases with the other inputs fixed, its unique path passes through one NOT and otherwise through AND/OR gates, so the output is nonincreasing in that input. The displayed positive witness for that input rules this out.

## Reproduction

From this directory run `python3 -B check_not_cones.py`. The check uses only the Python standard library. It prints the counts and verifies the seven witness pairs against the reference circuit. A local run took 0.22 seconds of elapsed time.
