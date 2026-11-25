import Upper
import L_meta_9399

namespace Table3687098

theorem exactSize :
    PEqualNP.Represents.repSize
      (fun u v : Fin 5 => (3687098 : ℕ).testBit (5 * u.val + v.val)) = 11 := by
  unfold PEqualNP.Represents.repSize
  apply le_antisymm
  · apply sInf_le
    exact ⟨11, rfl, atMostEleven⟩
  · apply le_sInf
    rintro _ ⟨k, rfl, C, hMono, hSize, hRep⟩
    have hk : 11 ≤ k := by
      by_contra! h
      exact PEqualNP.Outside.L_meta_9399 ⟨C, hMono, by omega, hRep⟩
    exact_mod_cast hk

end Table3687098
