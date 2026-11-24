# Petersen graph minus one vertex, with a prescribed first OR

For the L-meta-670 Petersen lower-bound search, the minimum with AND and OR alone is **16 gates**, both when the first gate is prescribed to be `x₀ OR x₆` and when the first gate is unrestricted. Allowing NOT gates leaves an open case. Every correct circuit, including one with NOT gates, has to read x₀ and x₆ again after that first OR. The [proposed reduction](R_meta_1677_1.lean) gives the two resulting searches on fourteen remaining gates. A reference from any follow-on search that uses these restrictions would establish downstream use.

The graph uses vertices 0 through 8. Its edges are 01, 12, 23, 34, 40, 05, 16, 27, 38, 57, 68 and 85. It has no four-cycle and its minimum vertex cover has size five. The task asks whether a binary AND/OR/NOT circuit with that first OR can compute its edge function using at most fifteen gates. The project has a [sixteen-gate upper bound with a different first gate](https://github.com/brilliant-hq/pequalnp-proofs/blob/main/lean/PEqualNP/Outside/L_meta_1001.lean). An [earlier attempt on the lower bound](https://github.com/brilliant-hq/pequalnp-proofs/pull/2954) received a rejection and later inconclusive checker verdicts.

## Why the two inputs must be read again

Fix vertices 4 and 6 to true, with all others false. Adding vertex 0 changes the answer from false to true because of edge 04. The first OR was already true. Its output and every other primary wire have the same values before and after the change, apart from x₀ itself. The remainder of the circuit therefore has to read x₀ directly. Similarly, on the set {0,8}, adding 6 creates edge 68 and leaves the first OR unchanged. Some later gate must read x₆ directly. The output cannot be a primary input because the target rejects every singleton and accepts the endpoints of an edge. Each other vertex is essential and occurs only among the original inputs, so it must also be read after the first gate.

The [Lean proof](FirstOr.lean) propagates agreement on all wires except one through a list of arbitrary deterministic gates. It allows an arbitrary output index and missing wires that evaluate to false. The specialization rules out both omissions for any target-computing gate output.

## An exhaustive monotone lower bound

Deleting any vertex gives a graph with at most eight vertices. The [previously verified bounds on those graphs](../L-meta-612/FiniteChecks.md) let the search restrict the number of gates that can disappear when that input is fixed to false. The unrestricted run excluded circuits of at most fifteen AND/OR gates. It expanded 136,631,381 live-wire states. A separate run for the prescribed OR excluded all circuits where its output and all nine original wires are used later, expanding 4,902,205 states. If that output is unused, deleting the gate leaves at most fourteen gates. The ordinary search excluded that budget in 13,013 states.

For the upper bound, use the five star centers 1, 0, 3, 7 and 8. The star at 1 uses `x₀ OR x₆` as its first gate and then adds x₂ to its neighbor arm. The other neighbor arms are {4,5}, {2,4,8}, {2,5} and {5,6}, respectively. The circuit has sixteen gates. Both this construction and a separately synthesized sixteen-gate circuit were checked on all 512 assignments. The [search transcript](SearchResults.txt) records the results and the synthesized gate values.

## Why all Boolean inputs matter with NOT gates

For a monotone circuit, testing the twelve edge inputs and twelve maximal independent sets determines agreement on all 512 inputs. With one NOT, a ten-gate circuit with the prescribed first gate passes all 24 tests and gives the wrong answer on 400 inputs. Its function is

```text
NOT ( (x₇ AND ((x₀ OR x₆) OR x₁))
   OR (x₂ AND (x₀ OR x₄))
   OR (x₅ AND (x₁ OR x₃)) ).
```

The seven pairs detected inside the NOT are all nonedges. Every maximal independent set contains one of those seven pairs. The circuit already fails on the empty input, where it returns true. [Executable check](check_examples.py)

## The remaining search

Remove the first gate, make its value available as a tenth input, and keep the original nine inputs. A circuit of size at most fifteen then gives a continuation of size at most fourteen. This holds even when the first output is unused. The two hypotheses of the proposed reduction exclude continuations without a NOT and continuations with at least one NOT, respectively. The monotone computation above supplies evidence for the former. Its finite computation has not been internalized as a Lean certificate for that hypothesis.

`fixed_first.py` encodes each later binary gate by its operation and its two earlier wire indices. A NOT repeats its unary operand in the inert second slot. The first OR is given its required value. A correct circuit can propagate constants, remove unary identity and unused gates, arrange its output last, and pad a shorter tail by repeating the output in idempotent ORs. These operations preserve the fixed first signal, which may be unused. Consequently an unsatisfiability proof on all 512 assignments would exclude every circuit at the budget. A satisfying model must be decoded and checked on every assignment before it establishes a counterexample. The search on all 512 inputs produced no verdict within the initial 90-second trial.

The reduction file's outer conclusion matches the posted statement. Its proof body was checked with Lean 4.36.0 on the circuit definitions and an equivalent fan-in predicate in an isolated interface. The official project build and checker verdict are separate.

## Reproduction

From this directory, use Python 3.10 or newer, a C++17 compiler and the project's Lean 4.36.0. The final argument to `--all-live-first-or` gives the second prescribed operand. This option starts the remaining schedule with every original input and the first OR output live. The preceding deletion run covers an unused first gate.

```sh
elan run leanprover/lean4:v4.36.0 lean FirstOr.lean
python3 -B check_examples.py
c++ -O3 -std=c++17 ../L-meta-612/kernel_search.cpp -o /tmp/petersen-search
/tmp/petersen-search 0 0 0 --smaller-optimal 18 < Graph.txt
/tmp/petersen-search 0 0 -1 --smaller-optimal 17 < Graph.txt
/tmp/petersen-search 0 0 0 --smaller-optimal 17 --all-live-first-or 0 6 < Graph.txt
/tmp/petersen-search 0 0 1 --smaller-optimal 17 --all-live-first-or 0 6 < Graph.txt > /tmp/petersen-upper.txt
python3 -B ../L-meta-612/verify_controls.py --smaller-optimal Graph.txt /tmp/petersen-upper.txt
```

The Lean toolchain includes CaDiCaL. The pinned positive control returns `SATISFIABLE`. The two omitted-input controls each return `UNSATISFIABLE`. The last command generates the remaining full-search instance.

```sh
python3 -B fixed_first.py /tmp/petersen-upper.cnf --gates 16 --pin-witness
elan run leanprover/lean4:v4.36.0 cadical -q -n /tmp/petersen-upper.cnf
python3 -B fixed_first.py /tmp/petersen-no-0.cnf --rows collision --omit 0
elan run leanprover/lean4:v4.36.0 cadical -q -n /tmp/petersen-no-0.cnf
python3 -B fixed_first.py /tmp/petersen-no-6.cnf --rows collision --omit 6
elan run leanprover/lean4:v4.36.0 cadical -q -n /tmp/petersen-no-6.cnf
python3 -B fixed_first.py /tmp/petersen-remaining.cnf --negation-branch
```
