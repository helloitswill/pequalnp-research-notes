# A 65-gate circuit for the order-three plane with a double read

The project's L-meta-1481 asks for an incidence circuit with at most 64 gates on the 13 points and 13 lines of PG(2,3). L-meta-1482 asks for a proof that such a circuit cannot exist. This construction satisfies every condition of L-meta-1481 at 65 gates. Lean proves existence at that budget. The 64-gate question remains open in this work. [Project desk](https://data.pequalnp.com/data/desk/gaps.json)

## Construction

Each line consists of the four translates of 0, 1, 3 and 9 by its index modulo 13. Three OR gates per line detect whether a selected point lies on it. Let `A` be the AND of the line-zero input and its point disjunction. Let `P` be the point disjunction for line one and `L` the line-one input. The output for these two lines is

```text
(A OR P) AND (A OR L) = A OR (P AND L).
```

The circuit combines this output with the eleven ordinary line terms. It uses 39 gates for the point disjunctions, one for `A`, three for the displayed expression, eleven for the other line terms and eleven to combine the twelve results.

Point zero lies on line zero and outside line one. On that incidence both factors of the final AND above must use `A`. The two marking recurrences in the posted problem both give false at the output. Lean checks the marked pair (0, 0). The executable check finds exactly three such pairs, (0, 0), (3, 0) and (9, 0).

## Verification

`PlaneDoubleRead.exists_65` in `DoubleRead65.lean` proves the posted existence statement with the bound changed from 64 to 65. The independent comparison used the exact text returned by the public desk and checked that L-meta-1482 negates L-meta-1481. Lean reported only `propext`, `Classical.choice` and `Quot.sound`. The proof uses a wire table to establish the circuit's value on an arbitrary input. It checks each gate's two distinct, earlier operands and the marking equations. [Pinned project and Lean dependencies](https://github.com/open-goat/pequalnp-proofs/tree/03100514f27f29747afd9b139e314a2125adc0c8/lean)

From the pinned project's `lean` directory, with `PEqualNP.Defs` built, the following commands compile the proof and verify its exact type and axioms. Set `proof_dir` to the absolute path of this directory.

```sh
lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; cd "$1" && lean -o DoubleRead65.olean DoubleRead65.lean && lean Exact65.lean' sh "$proof_dir"
```

The Python checks use only the standard library. From this directory run

```sh
python3 -B full_plane.py
python3 -B repair_search.py
python3 -B repair_search.py --diamond
```

The first command verifies every one of the 67,108,864 Boolean inputs, all 52 incidences and every single-gate bypass to an earlier wire in this circuit. For monotone circuits it suffices to test the 52 minimal positive assignments and 704 maximal negative assignments when testing a repair. The original circuit also passed the independent full truth table.

None of the 3,770 bypasses preserves incidence. Allowing one other gate to be replaced by any AND or OR of two distinct earlier wires also produced no equivalent circuit. In a further search, 169 first edits to the displayed three-gate expression were each followed by a bypass in that expression and one further unrestricted gate edit. The search found 273 equivalent repairs, counting edit descriptions. Every one lost the double-read condition. These results concern the specified circuit, ordering and edits.

## Searches on two or three lines

`patch_search.py` groups points that have exactly the same incidences on the selected lines into one input, implemented by a fixed OR. All other lines keep their standard circuits. The search synthesizes the replacement using CaDiCaL and checks every SAT witness against the entire truth table of the smaller problem.

At the standard gate budget, CaDiCaL returned UNSAT for both marked point types on two lines and on three concurrent lines. On two lines, one extra gate sufficed for a point private to the marked line. For three nonconcurrent lines the unrestricted 11-gate searches reached their 180-second limit for both marked point types. One example of each invocation follows. The solver path can be set with `--solver`.

```sh
python3 -B patch_search.py --lines 0 1 --point 0 --line 0 --extra 1
python3 -B patch_search.py --lines 0 12 10 --point 0 --line 0 --seconds 90
python3 -B patch_search.py --lines 0 1 2 --point 1 --line 0 --seconds 180
```
