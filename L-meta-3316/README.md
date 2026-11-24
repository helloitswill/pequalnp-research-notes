# A counterexample to L-meta-3316

The proposed Heawood-graph lemma quantifies over every predicate on 14 Boolean inputs. Choose the predicate that is true on exactly the inputs encoded by the three masks 127, 244 and 432. This refutes the universal lemma for any circuit size. [Parent reduction that introduced the lemma](https://github.com/brilliant-hq/pequalnp-proofs/blob/b4c5ce3d10a6b3b34639f508d0a3f01a1a8fd163/lean/PEqualNP/Outside/R_meta_2876_1.lean)

The order compares inputs bit by bit, with false below true. None of the three masks is contained in another, so each is a minimal true input of the chosen predicate. Every allowed pair in the lemma starts with one of these masks. At that first input the lemma requires the designated wires to differ, which makes their AND false. At the same input the requirement on minimal true inputs makes that AND true.

This settles the statement of L-meta-3316. The 26-gate question for the Heawood graph uses a specific edge predicate and remains open in this work.

## Reproduce the proof

Use the proof source in this directory and a checkout of `brilliant-hq/pequalnp-proofs` at `056ae7099a75e637daeae581dfdbd0a4c3713d4a`. From its `lean/` directory, run the following with Lean 4.36.0.

```sh
lake build +PEqualNP.Defs
lake env lean /path/to/Counterexample.lean
```

The second command exits successfully. The final theorem in [Counterexample.lean](Counterexample.lean) proves the negation of the posted statement, including its exact list of 13 wire-mask pairs.
