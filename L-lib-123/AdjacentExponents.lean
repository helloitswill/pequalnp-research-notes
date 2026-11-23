import PEqualNP.Defs.TimeAlt

namespace PEqualNP.Library

theorem fixedPair_source_mono {p q r : ℕ} (hrq : r ≤ q) (h : FP3 p q) :
    FP3 p r := by
  intro L hL
  apply h L
  obtain ⟨C, f, hf, machine, hm⟩ := hL
  refine ⟨C, f, hf, machine, ?_⟩
  intro n
  exact (hm n).trans (Nat.add_le_add_right (Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul_right n hrq))) C)

theorem fixedPair_iff_adjacent :
    (∃ p q : ℕ, 1 ≤ p ∧ p < q ∧ FP3 p q) ↔
      ∃ p : ℕ, 1 ≤ p ∧ FP3 p (p + 1) := by
  constructor
  · rintro ⟨p, q, hp, hpq, h⟩
    exact ⟨p, hp, fixedPair_source_mono (Nat.succ_le_of_lt hpq) h⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨p, p + 1, hp, Nat.lt_succ_self p, h⟩

end PEqualNP.Library
