# PEqualNP research notes

Independent work by [helloitswill](https://github.com/helloitswill), with AI assistance, on five questions posted by the [PEqualNP project](https://github.com/brilliant-hq/pequalnp-proofs). A six-vertex graph refutes the weighted circuit conjecture, and the cube circuit question has an exact computational answer. The three other questions remain open in this work.

## L-meta-662 · A counterexample to the weighted gate bound

A triangle with one private leaf at each corner has six edges, no four-cycle, and minimum vertex cover three. A circuit for its edge function has weighted size nine, one below the posted bound. Connected chains of these examples give arbitrarily large shortfalls. The [counterexample and reproducible checks](L-meta-662/README.md) give the circuit and its verification.

## L-meta-617 · How many gates detect an edge of the cube?

The minimum is **13** for two-input monotone AND/OR circuits, including circuits that reuse intermediate results. Lean checks a 13-gate circuit against the posted predicate. Two exhaustive programs exclude circuits of size 12 or smaller. A Lean certificate refutes the posted budget of 10. A short gate-elimination argument explains this lower bound using the six-cycle. The [cube result and reproduction instructions](L-meta-617/README.md) include the programs, construction, and written proof.

## L-gct-086 · How large can a constant-permanent space be?

Starting from the all-ones $n$ by $n$ matrix, how many independent complex directions can vary while its permanent stays equal to $n!$ everywhere? The project asks whether this number is always at most $Cn$ for a fixed constant $C$.

The [research notes](L-gct-086/RESEARCH.md) give a written proof of a sharp bound in one case. If the space has a basis whose matrices each have at most two nonzero entries, its maximum dimension is $2n-3$ for $n\ge 2$. The notes also give bounds for independently varying rows and for spaces with zero row and column sums. The general linear bound remains open.

One attempted argument would require the sum of fourth powers of entries to vanish on every centered level direction. [FourthMoment.lean](L-gct-086/FourthMoment.lean) checks an explicit 4 by 4 counterexample. The permanent stays 24 along the entire line, while the sum of fourth powers of the direction entries is 8. The [exact Python search](L-gct-086/search_rank_one.py) reproduces this example and enumerates a restricted family of rank-one directions through $n=12$. The [search output](L-gct-086/search-results.txt) and [Lean verification log](L-gct-086/lean-check.txt) are included.

## L-gct-190 · Searching for eight independent matrix directions

Start with the 5 by 5 all-ones matrix. The question asks whether one can vary it in eight independent complex directions while keeping its permanent equal to 120 everywhere in the resulting family.

We give a written proof that **seven is the maximum if cyclically permuting four rows preserves the whole family**. The same statement holds for columns by transposition. The proof allows arbitrary complex coefficients. A search for eight dimensions can therefore skip families invariant under any such row or column cycle. A single matrix with a symmetry can still belong to a family that breaks it.

- [Full upper bound and equality example](L-gct-190/FourRowCycle.md). The upper bound is a mathematical argument reviewed by a second reading.
- [Exact coefficient checker](L-gct-190/check_four_cycle.py). It verifies eight row weights and 125 polarized column cases used in the proof.
- [Seven-dimensional construction in Lean](L-gct-190/Seven.lean). This certifies the dimension and constant permanent of the explicit example.

Run the coefficient check from the repository root with `python3 L-gct-190/check_four_cycle.py`. Expected output is `Verified 8 row phases and 125 polarized column cases.`

## L-lib-123 · Checking a long computation in three rounds

The project asks whether three alternating blocks of guesses can save a fixed power of time on *every* deterministic computation in the stated time class.

- [Checkpoint argument and its limit](L-lib-123/CheckpointNotes.md). The argument replays a short stretch of a disputed computation. Its resource bound depends on how many bits the checkpoints take to write. See the note for the connection to the classical bounded-space simulation.
- [ThreeBlockCheckpoints.lean](L-lib-123/ThreeBlockCheckpoints.lean) proves the logical equivalence between accepting the three-round check and reaching the claimed endpoint. It also specifies which genuine checkpoints must fit the size budget on true and false claims. Implementing a verifier with the required time bound for unrestricted machines remains open.
- [AdjacentExponents.lean](L-lib-123/AdjacentExponents.lean) proves that it suffices to seek a pair of consecutive exponents in the project's exact formulation. [ConsumerExponent.lean](L-lib-123/ConsumerExponent.lean) checks the downstream exponent arithmetic conditional on finding such a pair.

## Reproducing the Lean checks

Use Lean 4.36.0. The net checks use the [revision pinned in the counterexample](L-meta-662/README.md). The cube checks use the [separate upstream revision and instructions given with the result](L-meta-617/README.md). The other three tasks use the definitions at [upstream commit 3789af2](https://github.com/brilliant-hq/pequalnp-proofs/tree/3789af288ba27735ae2428ee1beffa75180f24f6), which uses [Mathlib at fc4f59e](https://github.com/leanprover-community/mathlib4/tree/fc4f59e577feb1a4956671bc04ac18aaaf8cd842).

`lean L-lib-123/ThreeBlockCheckpoints.lean` needs only Lean's standard library. For the other files, use the upstream checkout's pinned Lake environment. Run `lake build PEqualNP.Defs.Gct PEqualNP.Defs.TimeAlt` from its `lean` directory, then run each file with `lake env lean` and the path to the file in this repository. Success is a zero exit status. Seven.lean also prints the axioms used for its final theorem.
