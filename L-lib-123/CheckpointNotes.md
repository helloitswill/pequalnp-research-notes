# Can three guesses verify a long computation faster?

L-lib-123 asks for one fixed pair of positive integers p < q such that every language decidable in deterministic time of order 2^(q m), for input length m, admits the project's three-block verifier with block length of order 2^(p m). This note records a partial result. The exact assignment remains open in this work.

## What the checker can challenge

A computation with a deterministic next step has a unique history once its initial state is fixed. Extend a halted history by repeating its final state. The three choices that verify a claimed endpoint are:

1. Supply a table of checkpoints from the initial state to the claimed endpoint.
2. Challenge one interval with a finer table that starts at its stated initial checkpoint and ends somewhere different from its stated endpoint.
3. Identify a pair of adjacent states in the challenge table with an incorrect transition. Replay just that segment.

For an honest outer table, every disagreeing challenge has a faulty segment. For a wrong answer, consider the first incorrect outer checkpoint. The challenger supplies the true history for the interval leading up to it. Every fine transition in this challenge is correct, so the third block cannot identify a fault. Invalid outer tables lose. A malformed challenge or one with a wrong start or an agreeing endpoint can be dismissed.

The file ThreeBlockCheckpoints.lean proves this equivalence for any deterministic step function and any finite number of coarse intervals, fine intervals and replay steps. The theorem restricted_tables_iff also allows arbitrary restrictions on which tables are admissible. For a true endpoint claim, it needs only the honest outer table to be admissible. For a false endpoint claim, it needs the honest inner table for each interval of the true run to be admissible. This points to a specific possible improvement: find compact representations that guarantee these two conditions and allow a fine transition to be checked quickly. The current file treats configurations as mathematical objects. It does not implement an encoding or a bounded-time multistack verifier.

## What it costs

With b intervals at each level, a verifier replays T/b² steps for a T-step computation, assuming integral block lengths or padding. If each relevant state can be written in S bits, either checkpoint table takes O(b S) bits, counting the fixed endpoints. The two costs balance at a budget of order (T S²)^(1/3) when 1 ≤ S ≤ T. The calculation assumes a fixed machine, direct local simulation, and linear processing of the tables. Input handling contributes the input length. This time-space tradeoff is classical. Fortnow and van Melkebeek's simulation appears as Lemma 2.7 in [Williams, Inductive Time-Space Lower Bounds for SAT and Related Problems](https://people.csail.mit.edu/rrw/ccc05.pdf).

For example, put T = 2^(4m) and take configurations of size O(2^m). With 2^m intervals at each level, a table and a final replay both cost O(2^(2m)). In the unrestricted assignment, a machine can keep a stack of order T. If the relevant checkpoints cost that much to write, the resulting bound is O(T). Even one explicitly stored checkpoint of that size would exceed every fixed sublinear power of T. This obstruction concerns the proposed protocol and its literal encoding. It leaves open the possibility of shorter, efficiently checkable representations, different machines for the same language, or a different proof.

## What Lean checked against the project

AdjacentExponents.lean proves that the exact posted existential statement is equivalent to asking for some p ≥ 1 with FP3 p (p+1). Any witness at (p,q) also works with source exponent p+1 by containment of deterministic time classes. The same three-block verifier and its constants apply. This reduces the number of unknown exponents by one. The argument supplies no witness for p.

Project revision 3789af288ba27735ae2428ee1beffa75180f24f6. Lean 4.36.0. Mathlib revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842. The [formal definition](https://github.com/brilliant-hq/pequalnp-proofs/blob/3789af288ba27735ae2428ee1beffa75180f24f6/lean/PEqualNP/Defs/TimeAlt.lean) specifies the model and [L122](https://github.com/brilliant-hq/pequalnp-proofs/blob/3789af288ba27735ae2428ee1beffa75180f24f6/lean/PEqualNP/Library/L122.lean) is the intended consumer.

Run `lean ThreeBlockCheckpoints.lean` with Lean 4.36.0. From the project's pinned Lean environment, build `lake build PEqualNP.Defs.TimeAlt`, then run `lake env lean /path/to/AdjacentExponents.lean`. Successful checks exit zero. Neither file declares an axiom or contains an unfinished proof. No proof PR or partial handoff was sent to the project.
