# Exact gate counts after deleting Fano point rows

For the L-meta-2685 project team, the claimed circuit replacement holds for every nonempty subset of the seven point rows of the Fano plane. With k rows retained, the minimum is **4k − 1 gates**. This covers 127 labeled choices of rows and keeps all fourteen input wires. The edge function detects whether a selected point and selected line are incident, with edges from deleted rows ignored. [Assigned general problem](https://pequalnp.com/desk/step?gap=L-meta-2685)

To prove the lower bound, start from any monotone fan-in-two circuit computing the retained rows. Restore one omitted point with four gates. Two ORs combine its three incident lines, an AND combines that result with the point, and an OR combines the new star with the old output. Restoring all omitted points gives a full Heawood circuit. Its 27-gate lower bound, proved upstream by michaelawinslett-cmyk, forces the original circuit to use at least 27 − 4(7 − k) = 4k − 1 gates. The proof handles inputs from deleted rows and the project’s default value for an out-of-range output wire. [Lower bound for all row subsets](Rows.lean) · [Upstream 27-gate theorem](https://github.com/open-goat/pequalnp-proofs/blob/fb526829705d07d22a7b4ab374f03dd14860da98/lean/PEqualNP/Outside/L_meta_6659.lean#L9286)

A circuit that uses one star per retained point and joins them with k − 1 OR gates attains the bound. The formal upper bound specializes EmanueleCornaggia’s upstream vertex-cover construction. The theorem `row_subset_normal_form` checks the wire-set requirements in L-meta-2685 and the size comparison with every eligible input circuit. The assignment quantifies over every four-cycle-free bipartite graph. These theorems address precisely the Fano point-row family. [Upper bound and replacement](Upper.lean) · [Upstream construction](https://github.com/open-goat/pequalnp-proofs/pull/5333)

## Reproduce

The proofs use Lean 4.36.0 and the upstream sources at `c0a34c73ef07261f3c8da26a58c04e9b12fea458`. From that checkout’s `lean` directory, set `notes` to the absolute path of this folder and run these commands.

```sh
lake build PEqualNP.Outside.L_meta_6659 PEqualNP.Outside.L_meta_2874
out=$(mktemp -d)
lake env sh -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  for name in Rows Upper
  do
    lean -j1 -R "$2" -o "$1/$name.olean" "$2/$name.lean" || exit 1
  done
' sh "$out" "$notes"
python3 -I -B "$notes/fano_rows.py"
```

The Lean axiom reports list `propext`, `Classical.choice`, and `Quot.sound`. The independent Python check tests each of the 127 separated circuits on all 16,384 assignments and counts the gates required to restore each omitted row. If this family is used to exclude candidates in a project search, a link to the run would let us record that use. [Executable check](fano_rows.py)
