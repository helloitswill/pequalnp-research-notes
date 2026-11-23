import Std

namespace ThreeBlockCheckpoints

-- A total deterministic step. A halted state can repeat itself.
def advance {C : Type} (step : C → C) : Nat → C → C
  | 0, x => x
  | n + 1, x => step (advance step n x)

private theorem advance_add {C : Type} (step : C → C) (x : C) (m n : Nat) :
    advance step (m + n) x = advance step n (advance step m x) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg step ih

private theorem advance_blocks {C : Type} (step : C → C) (x : C) (count size : Nat) :
    advance (advance step size) count x = advance step (count * size) x := by
  induction count with
  | zero => simp [advance, Nat.zero_mul]
  | succ n ih =>
    simp only [advance, ih, Nat.succ_mul, advance_add]

-- Equality of every adjacent transition forces all entries, including the last.
private theorem follows {C : Type} {F : C → C} {x : C} {n : Nat}
    (a : Fin (n + 1) → C) (h0 : a 0 = x)
    (h : ∀ i : Fin n, F (a i.castSucc) = a i.succ) :
    a (Fin.last n) = advance F n x := by
  have all (j : Nat) (hj : j ≤ n) : a ⟨j, by omega⟩ = advance F j x := by
    induction j with
    | zero => exact h0
    | succ j ih =>
      let i : Fin n := ⟨j, by omega⟩
      exact (h i).symm.trans (congrArg F (ih (by omega)))
  exact all n (Nat.le_refl n)

-- A disagreeing fine table with the correct start must contain a faulty edge
-- precisely when the claimed endpoint is correct.
theorem challenge_iff {C : Type} (F : C → C) (n : Nat) (x y : C) :
    (∀ table : Fin (n + 1) → C, table 0 = x → table (Fin.last n) ≠ y →
      ∃ j : Fin n, F (table j.castSucc) ≠ table j.succ) ↔
      advance F n x = y := by
  classical
  constructor
  · intro h
    apply Classical.byContradiction
    intro hbad
    let honest (j : Fin (n + 1)) := advance F j.val x
    obtain ⟨j, hj⟩ := h honest rfl hbad
    exact hj rfl
  · intro hend table hstart hwrong
    apply Classical.byContradiction
    intro h
    apply hwrong
    have edges (j : Fin n) : F (table j.castSucc) = table j.succ := by
      apply Classical.byContradiction
      intro bad
      exact h ⟨j, bad⟩
    exact (follows table hstart edges).trans hend

-- The three finite choices are a coarse table, a challenged interval together
-- with a fine table, and one faulty fine edge, respectively.
theorem three_block_iff {C : Type} (step : C → C)
    (coarse fine replay : Nat) (x y : C) :
    (∃ a : Fin (coarse + 1) → C, a 0 = x ∧ a (Fin.last coarse) = y ∧
      ∀ (i : Fin coarse) (b : Fin (fine + 1) → C),
        b 0 = a i.castSucc → b (Fin.last fine) ≠ a i.succ →
          ∃ j : Fin fine, advance step replay (b j.castSucc) ≠ b j.succ) ↔
      advance step (coarse * (fine * replay)) x = y := by
  let F := advance step replay
  let G := advance F fine
  have blocks : advance G coarse x = advance step (coarse * (fine * replay)) x := by
    calc
      advance G coarse x = advance F (coarse * fine) x := advance_blocks F x coarse fine
      _ = advance step ((coarse * fine) * replay) x := advance_blocks step x _ replay
      _ = _ := by rw [Nat.mul_assoc]
  constructor
  · rintro ⟨a, h0, hend, h⟩
    have edges (i : Fin coarse) : G (a i.castSucc) = a i.succ :=
      (challenge_iff F fine _ _).mp (h i)
    exact blocks.symm.trans ((follows a h0 edges).symm.trans hend)
  · intro h
    refine ⟨fun i => advance G i.val x, rfl, blocks.trans h, ?_⟩
    intro i
    exact (challenge_iff F fine _ _).mpr rfl

-- Restrict which tables fit the certificate budget. A correct claim only
-- needs its honest coarse table. For an incorrect claim, the honest fine
-- table must be available at each interval on the true run.
theorem restricted_tables_iff {C : Type} (F : C → C) (coarse fine : Nat) (x y : C)
    (allowCoarse : (Fin (coarse + 1) → C) → Prop)
    (allowFine : Fin coarse → (Fin (fine + 1) → C) → Prop)
    (a : Fin (coarse + 1) → C) (hstart : a 0 = x)
    (hstep : ∀ i : Fin coarse, advance F fine (a i.castSucc) = a i.succ)
    (hyes : a (Fin.last coarse) = y → allowCoarse a)
    (hno : a (Fin.last coarse) ≠ y → ∀ i : Fin coarse,
      allowFine i (fun j => advance F j.val (a i.castSucc))) :
    (∃ t : Fin (coarse + 1) → C, allowCoarse t ∧ t 0 = x ∧ t (Fin.last coarse) = y ∧
      ∀ (i : Fin coarse) (s : Fin (fine + 1) → C),
        allowFine i s → s 0 = t i.castSucc → s (Fin.last fine) ≠ t i.succ →
          ∃ j : Fin fine, F (s j.castSucc) ≠ s j.succ) ↔
      a (Fin.last coarse) = y := by
  classical
  constructor
  · rintro ⟨t, _, ht0, htend, verify⟩
    apply Classical.byContradiction
    intro hbad
    have agree (k : Nat) (hk : k ≤ coarse) : t ⟨k, by omega⟩ = a ⟨k, by omega⟩ := by
      induction k with
      | zero => exact ht0.trans hstart.symm
      | succ k ih =>
        let i : Fin coarse := ⟨k, by omega⟩
        have prev : t i.castSucc = a i.castSucc := ih (by omega)
        have nxt : advance F fine (a i.castSucc) = t i.succ := by
          apply Classical.byContradiction
          intro disagrees
          obtain ⟨j, mismatch⟩ := verify i _ (hno hbad i) prev.symm disagrees
          exact mismatch rfl
        exact nxt.symm.trans (hstep i)
    exact hbad ((agree coarse (Nat.le_refl coarse)).symm.trans htend)
  · intro yes
    refine ⟨a, hyes yes, hstart, yes, ?_⟩
    intro i s _ hs hy
    exact (challenge_iff F fine _ _).mpr (hstep i) s hs hy

end ThreeBlockCheckpoints
