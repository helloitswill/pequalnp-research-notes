import PEqualNP.Outside.L_meta_782

namespace PuncturedPlaneEncoders

open PEqualNP.CircuitLowerBounds

-- Isolating one point determines its line signal. With no selected points,
-- even a conditional requirement determines the auxiliary line signal.
theorem signals_of_star_outputs {n : ℕ} (S : Fin n → Finset (Fin n)) (m : Fin n)
    (C : Circuit) (o : Fin n → ℕ)
    (main : ∀ (P x : Fin n → Bool),
      (∃ p, p ≠ m ∧ P p = true ∧ (C.wires (List.ofFn x)).getD (o p) false = true) ↔
      ∃ p, p ≠ m ∧ P p = true ∧ ∃ l ∈ S p, x l = true)
    (aux : ∀ (P x : Fin n → Bool),
      (¬ ∃ p, p ≠ m ∧ P p = true ∧ ∃ l ∈ S p, x l = true) →
      ((C.wires (List.ofFn x)).getD (o m) false = true ↔ ∃ l ∈ S m, x l = true)) :
    ∀ p (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o p) false = true ↔
      ∃ l ∈ S p, x l = true := by
  intro p x
  by_cases h : p = m
  · subst p
    apply aux (fun _ => false) x
    rintro ⟨_, _, e, _⟩
    contradiction
  · let P : Fin n → Bool := fun q => decide (q = p)
    have one : P p = true := by simp [P]
    constructor
    · intro wire
      obtain ⟨q, _, bit, hit⟩ := (main P x).mp ⟨p, h, one, wire⟩
      have eq : q = p := of_decide_eq_true bit
      exact eq ▸ hit
    · intro hit
      obtain ⟨q, _, bit, wire⟩ := (main P x).mpr ⟨p, h, one, hit⟩
      have eq : q = p := of_decide_eq_true bit
      exact eq ▸ wire

private theorem profile_bound {n m k : ℕ} (S : Fin m → Finset (Fin n))
    (inter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (width : ∀ i, (S i).card = k + 1) (positive : 1 ≤ k)
    (C : Circuit) (o : Fin m → ℕ)
    (binary : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (correct : ∀ i (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = true ↔
      ∃ p ∈ S i, x p = true) : m * k ≤ C.size := by
  classical
  have sig (i : Fin m) :
      (Finset.univ.filter (fun a : Fin n =>
        (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)) = S i := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, correct, decide_eq_true_eq,
      exists_eq_right]
  have bound := PEqualNP.Outside.L_meta_782 n m k S C o (fun _ => k) inter
    (by intro i; rw [sig, width]; omega) binary
    (by intro i p active; simpa using (correct i _).mp active)
    (by
      intro i x _ outside
      cases h : (C.wires (List.ofFn x)).getD (o i) false with
      | false => rfl
      | true =>
        obtain ⟨p, hp, act⟩ := (correct i x).mp h
        rw [outside p hp] at act
        contradiction)
    (fun _ => le_rfl)
    (by intro i; rw [sig, width])
  simpa using bound

def fano (p : Fin 7) : Finset (Fin 7) :=
  Finset.univ.filter (fun l => p = l ∨ p = l + 1 ∨ p = l + 3)

theorem fano_encoder (C : Circuit) (o : Fin 7 → ℕ)
    (binary : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (correct : ∀ p (x : Fin 7 → Bool), (C.wires (List.ofFn x)).getD (o p) false = true ↔
      ∃ l ∈ fano p, x l = true) : 25 ≤ C.size + 6 + 5 := by
  have h := profile_bound (k := 2) fano (by decide +kernel) (by decide +kernel)
    (by decide) C o binary correct
  omega

def orderThree (p : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun l => (p.val + l.val + 1) % 13 ∈ [0, 1, 3, 9])

theorem order_three_encoder (C : Circuit) (o : Fin 13 → ℕ)
    (binary : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (correct : ∀ p (x : Fin 13 → Bool), (C.wires (List.ofFn x)).getD (o p) false = true ↔
      ∃ l ∈ orderThree p, x l = true) : 62 ≤ C.size + 12 + 11 := by
  have h := profile_bound (k := 3) orderThree (by decide +kernel) (by decide +kernel)
    (by decide) C o binary correct
  omega

end PuncturedPlaneEncoders
