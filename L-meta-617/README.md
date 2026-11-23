# L-meta-617 · Exact monotone circuit size for the cube edge function

**Thirteen gates are necessary and sufficient.** Put one Boolean input at each vertex of the three-dimensional cube. The output should be true exactly when the two ends of at least one edge are both true. The project asks whether a circuit of at most ten AND/OR gates, each reading at most two wires, can do this. The result refutes that existence statement. Intermediate gates may feed multiple later gates.

| Claim | Evidence |
|---|---|
| Thirteen gates suffice | [Lean witness](Upper13.lean) verified on the exact eight-input predicate in the project's circuit model |
| Twelve gates or fewer are impossible | [Python search](check_cube.py) and [C++17 search](row_search.cpp), using different state representations |
| Ten gates or fewer are impossible | [Written gate-elimination proof](ExcludeTen.md) using the project's checked six-cycle theorem, with a [small graph checker](verify_graph.py) |

## The 13-gate circuit

Number the cube vertices from 0 through 7 in binary. An edge changes exactly one bit. The vertices 0, 3, 5, and 6 form one side of the cube. Each has three neighbors on the other side. Compute two shared signals, $A=x_1 \lor x_2$ and $B=x_4 \lor x_7$. Use one OR and one AND for each row below.

| Vertex | Signal detecting an incident active edge |
|---|---|
| 0 | $x_0 \land (A \lor x_4)$ |
| 3 | $x_3 \land (A \lor x_7)$ |
| 5 | $x_5 \land (B \lor x_1)$ |
| 6 | $x_6 \land (B \lor x_2)$ |

Combining the four signals takes three final OR gates. The total is $2+8+3=13$.

## Why the searches cover all smaller circuits

1. Simplify constants, missing references, unary gates and gates with repeated operands, then remove gates outside the output's dependency cone. These operations preserve the output and never increase the gate count. Every cube input is essential because switching it on alongside a single neighbor can change the answer.
2. Monotonicity reduces the truth table to 18 assignments. There are 12 minimal true assignments (one per edge) and six maximal false assignments (the two parity classes and the four antipodal pairs). Every true assignment contains a minimal one, and every false assignment is contained in a maximal one. Both programs derive these assignments directly from the graph.
3. Start with eight live input wires. Choose any two live wires and compute their AND or OR. Keep each operand if a later gate needs it, and allow either or both to be dropped after their last use. Each normalized circuit has such a schedule. This includes circuits with shared gates. With $r$ gates left, at most $r+1$ wires can still be needed, since one binary gate can reduce their number by at most one. In particular, after $d$ gates in a circuit of size at most 12, the width is at most $\min(8+d,13-d)\le 10$.
4. A viable state must still distinguish each minimal true assignment from each maximal false one. If every live wire has value on the true assignment less than or equal to its value on the false assignment, every monotone continuation preserves this ordering. Such a state can be discarded.
5. The Python program records each live wire's values on the 18 assignments. It tracks which wires distinguish each of the 72 true/false pairs. It can substitute an existing wire or propagate a constant when a candidate has the same boundary values, because the resulting circuit is still monotone and agrees on the boundary. The C++ program instead records the vectors of live values for each assignment. It deduplicates equal vectors within each class and tests the ordering directly. Both programs reuse previously explored states. Neither uses a symmetry assumption on the eight inputs.

## Reproduce the computational lower bound

From this directory, run the following with Python 3 and a C++17 compiler.

```sh
python3 verify_graph.py
python3 check_cube.py 12
c++ -std=c++17 -O3 row_search.cpp -o row_search
./row_search 12
```

Python reports `result=NONE` after expanding 216,952 states. C++ reports `NONE` with 946,866 states and 69,406,358 transitions. These are exhaustive computational lower bounds. The human-readable proof in [ExcludeTen.md](ExcludeTen.md) gives the weaker lower bound of 11 by a separate argument.

## Reproduce the Lean upper bound

Use Lean 4.36.0 and the pinned Mathlib from [upstream commit 687a075](https://github.com/brilliant-hq/pequalnp-proofs/tree/687a0753bb65edc3dae1e25dee238905156733dd). From the upstream checkout's `lean` directory, run the following, substituting the path to your copy of these notes.

```sh
lake build PEqualNP.Defs.MetaComplexityLgpMono
lake env lean /path/to/pequalnp-research-notes/L-meta-617/Upper13.lean
```

The theorem `CubeEdgeUpper.thirteen_gates_suffice` gives a gate list and checks its output on all 256 inputs. It uses Lean's kernel evaluation.
