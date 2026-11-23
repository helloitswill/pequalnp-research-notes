import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! The ordered three-edge matching sum of a doubly centered matrix. -/
namespace PermanentLevel.Centered

open scoped BigOperators
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def distinctThree (f : ι → ι → ι → ℂ) : ℂ :=
  ∑ i, ∑ j ∈ univ.erase i, ∑ k ∈ (univ.erase i).erase j, f i j k

omit [Fintype ι] in
private lemma sum_without (s : Finset ι) (i : ι) (hi : i ∈ s) (f : ι → ℂ) :
    ∑ j ∈ s.erase i, f j = (∑ j ∈ s, f j) - f i := by
  have h := Finset.sum_erase_add s f hi
  linear_combination h

theorem three_vectors (f g h : ι → ℂ)
    (hf : ∑ i, f i = 0) (hg : ∑ i, g i = 0) (hh : ∑ i, h i = 0) :
    distinctThree (fun i j k => f i * g j * h k) = 2 * ∑ i, f i * g i * h i := by
  classical
  have each (i : ι) : (∑ j ∈ univ.erase i, ∑ k ∈ (univ.erase i).erase j,
      f i * g j * h k) = 2 * (f i * g i * h i) - f i * ∑ j, g j * h j := by
    calc
      _ = ∑ j ∈ univ.erase i, ((-f i * h i) * g j + (-f i) * (g j * h j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.mul_sum, sum_without _ _ hj, sum_without _ _ (mem_univ i), hh]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          sum_without _ _ (mem_univ i), sum_without _ _ (mem_univ i), hg]
        ring
  unfold distinctThree
  simp_rw [each]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hf, zero_mul, sub_zero]

private theorem sum_out {κ : Type*} (s : Finset κ) (q : κ → ι → ι → ι → ℂ) :
    distinctThree (fun i j k => ∑ t ∈ s, q t i j k) = ∑ t ∈ s, distinctThree (q t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [distinctThree]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [← ih]
    simp [distinctThree, Finset.sum_add_distrib]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Distinct ordered row and column triples give four times the cubic entrywise sum. -/
theorem centered_matching_three (t : ι → κ → ℂ)
    (hr : ∀ i, ∑ j, t i j = 0) (hc : ∀ j, ∑ i, t i j = 0) :
    distinctThree (fun i j k => distinctThree (fun x y z => t i x * t j y * t k z))
      = 4 * ∑ l, ∑ i, (t i l)^3 := by
  calc
    _ = distinctThree (fun i j k => 2 * ∑ l, t i l * t j l * t k l) := by
      congr 1
      funext i j k
      exact three_vectors _ _ _ (hr i) (hr j) (hr k)
    _ = ∑ l, distinctThree (fun i j k => 2 * (t i l * t j l * t k l)) := by
      simp_rw [Finset.mul_sum]
      exact sum_out _ _
    _ = ∑ l, 4 * ∑ i, (t i l)^3 := by
      apply Finset.sum_congr rfl
      intro l _
      have hh := three_vectors (fun i => t i l) (fun i => t i l) (fun i => t i l)
        (hc l) (hc l) (hc l)
      calc
        _ = 2 * distinctThree (fun i j k => t i l * t j l * t k l) := by
          simp only [distinctThree, Finset.mul_sum]
        _ = _ := by rw [hh]; simp only [pow_succ, pow_zero, one_mul]; ring
    _ = _ := (Finset.mul_sum ..).symm

end PermanentLevel.Centered
#print axioms PermanentLevel.Centered.centered_matching_three

