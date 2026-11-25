# A gate bound for two punctured-plane circuit searches

A search for a 24-gate Fano circuit or a 61-gate order-three circuit can skip the following family. First a shared circuit reads only the line variables and supplies one signal for each point, including the missing point. The main output ANDs each remaining point variable with its signal and ORs the resulting products. The auxiliary output is the signal of the missing point. In this family the exact minima are **25 gates for the Fano plane** and **62 gates for the plane of order three**. The project's assigned problems also allow gates to mix point and line variables at earlier stages. [Fano assignment](https://pequalnp.com/desk/step?gap=L-meta-6659) · [Order-three assignment](https://pequalnp.com/desk/step?gap=L-meta-2215)

Selecting just one point forces its line signal to equal the OR of all lines through that point. Selecting no points forces the missing point’s signal to equal the corresponding OR. This second argument works even on the order-three assignment, where the auxiliary output is only prescribed when the main output is false. [Signal argument](PencilEncoders.lean)

Two distinct points of either plane share exactly one line. The existing project theorem L-meta-782 therefore charges at least two preprocessing gates to each of the seven Fano points, and three to each of the thirteen points of the larger plane. The totals are 14 + 6 + 5 = 25 and 39 + 12 + 11 = 62. Computing each OR separately and then using the specified products and final ORs attains both counts. This is a specialization of k-sandhu’s checked counting result. The lower bounds and arithmetic are checked in Lean. The matching constructions are described here by their gate counts. [Specializations](PencilEncoders.lean) · [Upstream counting result](https://github.com/open-goat/pequalnp-proofs/blob/056ae7099a75e637daeae581dfdbd0a4c3713d4a/lean/PEqualNP/Outside/L_meta_782.lean)

The order-three task also allows unary and nullary gates. The accompanying normalization lemma applies the project's gate-elimination pass to all designated outputs at once. Every nonconstant output keeps a wire in the resulting circuit, every emitted gate is binary AND or OR, and the size can only decrease. Thus the same 62-gate bound holds for the allowed fan-in of at most two. [Simultaneous normalization](PencilNormalization.lean) · [Project elimination pass](https://github.com/open-goat/pequalnp-proofs/blob/056ae7099a75e637daeae581dfdbd0a4c3713d4a/lean/PEqualNP/MetaComplexity/Helpers/Elim.lean)

## Check the proofs

With the project's Lean 4.36.0 checkout at commit `056ae7099a75e637daeae581dfdbd0a4c3713d4a`, set `notes` to the absolute path of this folder. From the project's `lean` directory run the following commands.

```sh
lake build PEqualNP.Outside.L_meta_782 PEqualNP.MetaComplexity.Helpers.Elim
out=$(mktemp -d)
lake env sh -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  for name in PencilEncoders PencilNormalization
  do
    lean -R "$2" -o "$1/$name.olean" "$2/$name.lean" || exit 1
  done
' sh "$out" "$notes"
```

If you use the bound in a synthesis run, a link to the configuration that excludes this family would let us record the downstream use.
