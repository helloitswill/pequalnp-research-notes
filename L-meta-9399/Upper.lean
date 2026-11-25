import PEqualNP.Defs

namespace Table3687098

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [11, 8]⟩,
    ⟨.and, [12, 13]⟩, ⟨.or, [11, 10]⟩, ⟨.or, [15, 2]⟩,
    ⟨.or, [16, 3]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [17, 18]⟩, ⟨.or, [14, 19]⟩], 20⟩

theorem atMostEleven :
    PEqualNP.Represents.RepSizeAtMost
      (fun u v : Fin 5 => (3687098 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · intro gate hm
    simp [circuit] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h <;> subst gate <;> simp
  · decide +kernel

end Table3687098
