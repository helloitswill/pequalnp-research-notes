# Eleven gates are necessary and sufficient for graph 3687098

In task L-meta-9399 the input selects one of five rows and one of five columns. The output must equal the corresponding graph entry. The minimum number of AND/OR gates of fan-in at most two is **11**. The rows, in column order starting at zero, are `01011`, `10101`, `00001`, `00001`, and `11000`.

The lower bound follows from a Lean certificate that rules out every circuit with at most ten gates. It tracks which wire values can still distinguish each positive entry from each negative entry. Lean checks that every possible circuit is accounted for and verifies every step of the finite search. The search argument adapts the project's earlier four-by-four case. [Submitted lower bound](https://github.com/open-goat/pequalnp-proofs/pull/13448/files) · [Earlier four-by-four proof](https://github.com/open-goat/pequalnp-proofs/blob/e7f111b1ab64faf2fb69fc9ce9c74195721af0fb/lean/PEqualNP/Outside/L_meta_6340.lean)

The upper bound gives an explicit eleven-gate circuit. Wires 0 through 4 select the row and wires 5 through 9 select the column. Each gate appends its output to the wire list, and wire 20 is the final result. Lean verifies the gate count, the gate types and all 25 outputs. [Circuit and proof](Upper.lean)

The final Lean theorem states that the project's minimum circuit size, `Represents.repSize`, equals 11 for this graph. It combines the two bounds. [Exact-size proof](Exact.lean)

## Reproduction

Use the project's pinned Lean 4.36.0 environment with `PEqualNP.Defs` built. In a fresh scratch directory, place `Upper.lean`, `Exact.lean`, and the [submitted lower-bound file](https://raw.githubusercontent.com/helloitswill/pequalnp-proofs/1cef19819d6c298e48d036dcc71a5436ad99cde0/lean/PEqualNP/Outside/L_meta_9399.lean) under their original filenames. From the pinned checkout's `lean` directory, run these commands with `proofdir` set to the absolute path of the scratch directory.

```sh
leanexe="$(lake env which lean)"
export LEAN_PATH="$proofdir:$(lake env printenv LEAN_PATH)"
(cd "$proofdir" && "$leanexe" -o Upper.olean Upper.lean && "$leanexe" -o L_meta_9399.olean L_meta_9399.lean && "$leanexe" Exact.lean)
```

The last command succeeds when Lean verifies the equality. The project's own checker reads the lower bound against its posted text in an independent run. [Pinned checker run](https://github.com/helloitswill/pequalnp-research-notes/actions/runs/45603391947)
