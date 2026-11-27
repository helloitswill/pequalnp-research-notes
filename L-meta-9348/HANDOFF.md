# Fourteen rectangles after removing a row or column

On 27 November 2026, Lean 4.36.0 checked that deleting any one row or any one column of the project's 21 × 21 matrix leaves a zero set covered by 14 all-zero rectangles. In particular, every submatrix with fewer than 21 rows or fewer than 21 columns admits such a cover. A lower-bound proof based on an induced submatrix must therefore use all the rows and columns to rule out 14 rectangles. The full-matrix question remains open in this work. [Project unit L-meta-9348](https://pequalnp.com/desk/step?gap=L-meta-9348)

## Certificates

The first list in the proof covers exactly 334 of the 336 zeros and includes no ones. Its two uncovered cells have zero-based coordinates (11, 12) and (12, 20). A second list covers every zero outside row 0. Simultaneously shifting row and column indices gives all 21 row deletions. Transposition followed by negating the indices gives the 21 column deletions. [Reviewed Lean file](https://github.com/helloitswill/pequalnp-research-notes/blob/021ccc97842fb87a4a430ceba484ed7010c36353/L-meta-9348/PuncturedPlaneCover.lean)

This command checks the proof from this directory.

```sh
lean +leanprover/lean4:v4.36.0 PuncturedPlaneCover.lean
```

A fresh directory containing only the source compiled with exit code 0. A separate Lean process reported only `propext`, `Classical.choice` and `Quot.sound` across the four reported theorems. The SHA-256 of the file is `70d011906e5031e558d219a4f4628ca50eea99f749ce7d7dbbefb7b5781eb720`. A separate Python check read the matrix from the live desk statement, compared both occurrences with the proof and independently tested every cell of all 42 deletions.

## Completing the cover

An exact Python search tested all 3,003 ways to remove six rectangles from the 334-cell cover and keep the other eight. In each case it tested whether six new all-zero rectangles could cover the remaining cells. Two cases had seven pairwise incompatible cells. Exhaustive coloring excluded the other 3,001 cases. Any full 14-rectangle cover must therefore change at least seven of the listed rectangles. This search result was checked in Python. It is separate from the four Lean theorems. [Search source](repair_cover.py)

```sh
python3 -B repair_cover.py 6
```

## Publication and desk status

Contributor `helloitswill` opened the research-notes PR on 27 November 2026. The published Lean source matches the local replay at commit `021ccc97842fb87a4a430ceba484ed7010c36353`. The replacement checker was added in commit `e59d1f8af84735955fe10b41e58ea1761197d999`. The intended audience is the project team studying the full cover and its negation. Direct acknowledgment and downstream use are unconfirmed. [Research-notes PR 1](https://github.com/helloitswill/pequalnp-research-notes/pull/1)

This result extends the previously assigned matrix problem L-meta-9361. The public board at 07:26 UTC listed zero ordinary units available and one holder for L-meta-9348. The assignment endpoint returned an empty response with a 300-second retry. No new lease was issued at that check. The posted full-matrix theorem has no upstream submission from this work. [Live desk](https://pequalnp.com/desk)
