import Mathlib.Data.Finset.Powerset
import PEqualNP.Defs.Gct

/-!
For a fixed matrix, allow each row to be kept or set to zero independently.
The permanent is constant on all of these choices precisely when every
nonempty subset of rows has zero matching coefficient. This works in every
matrix size and uses the project's permanent polynomial.
-/

namespace PermanentLevel

open Finset
open scoped BigOperators

variable {n : ℕ}

/-- The coefficient on a specified collection of rows, counting full permutations. -/
noncomputable def matching (u : Matrix (Fin n) (Fin n) ℂ) (s : Finset (Fin n)) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ∏ i ∈ s, u i (σ i)

/-- Add the selected perturbation rows to the all-ones matrix. -/
noncomputable def onRows (u : Matrix (Fin n) (Fin n) ℂ) (s : Finset (Fin n)) : ℂ :=
  MvPolynomial.eval (fun p : Fin n × Fin n => 1 + if p.1 ∈ s then u p.1 p.2 else 0)
    (PEqualNP.Gct.permPoly ℂ n)

theorem matching_empty (u : Matrix (Fin n) (Fin n) ℂ) :
    matching u ∅ = (n.factorial : ℂ) := by
  classical
  simp [matching, Fintype.card_perm]

theorem onRows_eq_sum (u : Matrix (Fin n) (Fin n) ℂ) (s : Finset (Fin n)) :
    onRows u s = ∑ t ∈ s.powerset, matching u t := by
  classical
  let a : Matrix (Fin n) (Fin n) ℂ := fun i j => 1 + if i ∈ s then u i j else 0
  have heval : onRows u s = a.permanent := by
    simp [onRows, PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply, a]
  rw [heval, ← Matrix.permanent_transpose, Matrix.permanent]
  simp only [Matrix.transpose_apply]
  calc
    ∑ σ : Equiv.Perm (Fin n), ∏ i, a i (σ i)
        = ∑ σ : Equiv.Perm (Fin n), ∏ i ∈ s, (1 + u i (σ i)) := by
          apply Finset.sum_congr rfl
          intro σ _
          calc
            ∏ i, a i (σ i) = ∏ i ∈ s, a i (σ i) := by
              symm
              exact Finset.prod_subset (Finset.subset_univ _) fun i _ hi => by simp [a, hi]
            _ = _ := Finset.prod_congr rfl fun i hi => by simp [a, hi]
    _ = ∑ t ∈ s.powerset, matching u t := by
          simp_rw [Finset.prod_one_add]
          exact Finset.sum_comm

theorem onRows_constant_iff (u : Matrix (Fin n) (Fin n) ℂ) :
    (∀ s, onRows u s = (n.factorial : ℂ)) ↔
      ∀ s, s.Nonempty → matching u s = 0 := by
  classical
  constructor
  · intro h s
    induction s using Finset.strongInductionOn
    rename_i s ih
    intro hs
    have hz : ∑ t ∈ (s.powerset.erase s).erase ∅, matching u t = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have hne := (Finset.mem_erase.mp ht).1
      obtain ⟨hneS, hp⟩ := Finset.mem_erase.mp (Finset.mem_erase.mp ht).2
      exact ih t (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hp, hneS⟩)
        (Finset.nonempty_iff_ne_empty.mpr hne)
    have he : ∅ ∈ s.powerset.erase s :=
      Finset.mem_erase.mpr ⟨Ne.symm hs.ne_empty, by simp⟩
    have hm : s ∈ s.powerset := by simp
    have allTerms := h s
    rw [onRows_eq_sum, ← Finset.sum_erase_add _ _ hm, ← Finset.sum_erase_add _ _ he,
      hz, matching_empty] at allTerms
    simpa using allTerms
  · intro h s
    rw [onRows_eq_sum, ← matching_empty u]
    apply Finset.sum_eq_single ∅
    · intro t _ ht
      exact h t (Finset.nonempty_iff_ne_empty.mpr ht)
    · simp

/-- Permuting columns scales each matching on exactly the rows in s. -/
theorem matching_weight (u : Matrix (Fin n) (Fin n) ℂ) (rot : Equiv.Perm (Fin n))
    (a : ℂ) (h : ∀ i j, u i (rot j) = a * u i j) (s : Finset (Fin n)) :
    matching u s = a ^ s.card * matching u s := by
  classical
  unfold matching
  calc
    (∑ σ : Equiv.Perm (Fin n), ∏ i ∈ s, u i (σ i)) =
        ∑ σ : Equiv.Perm (Fin n), ∏ i ∈ s, u i ((rot * σ) i) :=
      ((Group.mulLeft_bijective rot).sum_comp
        (fun σ : Equiv.Perm (Fin n) => ∏ i ∈ s, u i (σ i))).symm
    _ = _ := by simp only [Equiv.Perm.mul_apply, h, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.mul_sum]

/-- If a column permutation scales a matrix by a scalar whose short powers never equal
one, and the matrix uses only that many rows, its entire line has constant permanent. -/
theorem level_of_rotation (u : Matrix (Fin n) (Fin n) ℂ) (rot : Equiv.Perm (Fin n))
    (a : ℂ) (h : ∀ i j, u i (rot j) = a * u i j) (S : Finset (Fin n))
    (supported : ∀ i, i ∉ S → ∀ j, u i j = 0)
    (avoid : ∀ k, 0 < k → k ≤ S.card → a ^ k ≠ 1) (z : ℂ) :
    MvPolynomial.eval (fun p : Fin n × Fin n => 1 + z * u p.1 p.2)
      (PEqualNP.Gct.permPoly ℂ n) = (n.factorial : ℂ) := by
  classical
  let v : Matrix (Fin n) (Fin n) ℂ := fun i j => z * u i j
  have hv (i j) : v i (rot j) = a * v i j := by simp [v, h, mul_left_comm]
  have vanish (s : Finset (Fin n)) (hs : s.Nonempty) : matching v s = 0 := by
    by_cases hsub : s ⊆ S
    · have hw := matching_weight v rot a hv s
      have zero : (1-a^s.card) * matching v s = 0 := by rw [sub_mul, one_mul, ← hw, sub_self]
      exact (mul_eq_zero.mp zero).resolve_left
        (sub_ne_zero.mpr (Ne.symm (avoid _ (Finset.card_pos.mpr hs) (Finset.card_le_card hsub))))
    · obtain ⟨i, hi, hout⟩ := Finset.not_subset.mp hsub
      exact Finset.sum_eq_zero fun σ _ => Finset.prod_eq_zero hi (by simp [v, supported i hout])
  simpa [onRows, v] using (onRows_constant_iff v).2 vanish Finset.univ

end PermanentLevel
#print axioms PermanentLevel.onRows_constant_iff

#print axioms PermanentLevel.level_of_rotation
