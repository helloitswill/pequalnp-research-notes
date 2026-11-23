import Mathlib.Tactic.Ring

-- Check the rational exponent that would use any witness to L-lib-123 in L-lib-122.
theorem consumerExponent (p q : ℕ) (hp : 1 ≤ p) (hpq : p < q) :
    p * (4*p + 1)^3 < q * (4*p)^3 := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hp
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hpq)
  simp only [Nat.succ_eq_add_one]
  ring_nf
  omega
