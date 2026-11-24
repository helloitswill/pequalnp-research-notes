import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace HeawoodPairCounterexample

def row (mask : ℕ) : Fin 14 → Bool := fun i => mask.testBit i.val

def mask (i : Fin 3) : ℕ := ([127, 244, 432] : List ℕ).getD i.val 0

def selected (x : Fin 14 → Bool) : Prop := ∃ i : Fin 3, x = row (mask i)

theorem minimal_selected (i : Fin 3) : Minimal selected (row (mask i)) := by
  have incomparable : ∀ j k : Fin 3, row (mask j) ≤ row (mask k) → j = k := by decide
  refine ⟨⟨i, rfl⟩, ?_⟩
  intro y hy le
  obtain ⟨j, rfl⟩ := hy
  obtain rfl := incomparable j i le
  exact le_rfl

end HeawoodPairCounterexample

open HeawoodPairCounterexample

theorem heawood_pair_refuted : ¬ (∀ (x1 : (Fin (14 : ℕ) → Bool) → Prop),   ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.GateOp) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ × ℕ),     PEqualNP.MetaComplexity.Monotone2 x2 ∧       x2.size ≤ (25 : ℕ) ∧         (14 : ℕ) ≤ x4 ∧           x4 < x5 ∧             x5 < (14 : ℕ) + x2.size ∧               (x3 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x6 ∈ [((127 : ℕ), (244 : ℕ)), ((127 : ℕ), (432 : ℕ)), ((127 : ℕ), (3716 : ℕ)), ((127 : ℕ), (16256 : ℕ)), ((244 : ℕ), (314 : ℕ)), ((244 : ℕ), (432 : ℕ)), ((244 : ℕ), (792 : ℕ)), ((244 : ℕ), (1290 : ℕ)), ((244 : ℕ), (3716 : ℕ)), ((244 : ℕ), (7426 : ℕ)), ((432 : ℕ), (660 : ℕ)), ((432 : ℕ), (1220 : ℕ)), ((432 : ℕ), (1548 : ℕ))]) ∧                 have x7 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x7 : ℕ) (x8 : Fin (14 : ℕ) → Bool) => (x2.wires (List.ofFn x8)).getD x7 Bool.false;                 have x8 : Fin (14 : ℕ) → Bool := fun (x8 : Fin (14 : ℕ)) => x6.1.testBit ↑x8;                 have x9 : Fin (14 : ℕ) → Bool := fun (x9 : Fin (14 : ℕ)) => x6.2.testBit ↑x9;                 have x10 : (Fin (14 : ℕ) → Bool) → Bool := fun (x10 : Fin (14 : ℕ) → Bool) => x3.eval [x7 x4 x10, x7 x5 x10];                 x7 x4 x8 ≠ x7 x5 x8 ∧ x7 x4 x8 = x7 x5 x9 ∧ x7 x5 x8 = x7 x4 x9 ∧ (∀ (x11 : Fin (14 : ℕ) → Bool), Minimal x1 x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.true) ∧ ∀ (x11 : Fin (14 : ℕ) → Bool), Maximal (fun (x12 : Fin (14 : ℕ) → Bool) => ¬x1 x12) x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.false) := by
  intro claimed
  obtain ⟨C, op, a, b, p, _, _, _, _, _, ⟨hop, mem⟩, tail⟩ := claimed selected
  subst op
  obtain ⟨different, _, _, positive, _⟩ := tail
  have first : p.1 = 127 ∨ p.1 = 244 ∨ p.1 = 432 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst p <;> decide
  have smallest : Minimal selected (row p.1) := by
    rcases first with h | h | h
    · rw [h]; exact minimal_selected 0
    · rw [h]; exact minimal_selected 1
    · rw [h]; exact minimal_selected 2
  rcases positive (row p.1) smallest with impossible | both
  · cases impossible.1
  · have eqs : (C.wires (List.ofFn (row p.1))).getD a false = true ∧
        (C.wires (List.ofFn (row p.1))).getD b false = true := by
      simpa [GateOp.eval] using both
    exact different (eqs.1.trans eqs.2.symm)
