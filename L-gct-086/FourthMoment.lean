import PEqualNP.Defs.Gct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-! A centered flat line whose fourth entrywise power sum is nonzero. -/
namespace PermanentLevel.FourthMoment

open scoped BigOperators
private abbrev I4 := Fin 4
private noncomputable def a : I4 → ℂ := ![1, -1, 0, 0]
private noncomputable def b : I4 → ℂ := ![1, Complex.I, -1, -Complex.I]
noncomputable def direction (p : Fin 4 × Fin 4) : ℂ := a p.1 * b p.2

theorem row_sum (i : Fin 4) : ∑ j : Fin 4, direction (i,j) = 0 := by
  simp [direction, Fin.sum_univ_four, b]

theorem col_sum (j : Fin 4) : ∑ i : Fin 4, direction (i,j) = 0 := by
  simp [direction, Fin.sum_univ_four, a]

theorem fourth_power_sum : ∑ i : Fin 4, ∑ j : Fin 4, direction (i,j) ^ 4 = 8 := by
  norm_num [direction, a, b, Fin.sum_univ_four, pow_succ, Complex.I_mul_I]

private noncomputable def mat (z : ℂ) : Matrix I4 I4 ℂ :=
  fun i j => 1 + z * direction (i,j)

private def rotate : Equiv.Perm I4 := Equiv.addRight 1

private theorem rotate_b (j : I4) : b (rotate j) = Complex.I * b j := by
  fin_cases j <;> norm_num [rotate, b, Equiv.addRight, Complex.I_mul_I]

private theorem rotate_perm (z : ℂ) : (mat (Complex.I*z)).permanent = (mat z).permanent := by
  have hmat : mat (Complex.I*z) = (mat z).submatrix id rotate := by
    ext i j
    simp only [mat, Matrix.submatrix_apply, id_eq, direction, rotate_b]
    ring
  rw [hmat, Matrix.permanent_permute_rows]

private theorem by_perm (z : ℂ) : (mat z).permanent =
    ∑ σ : Equiv.Perm I4, (1+z*b (σ 0)) * (1-z*b (σ 1)) := by
  rw [← Matrix.permanent_transpose, Matrix.permanent]
  apply Finset.sum_congr rfl
  intro σ _
  simp [Matrix.transpose_apply, mat, direction, a, Fin.prod_univ_four, sub_eq_add_neg]

theorem level (z : ℂ) :
    MvPolynomial.eval (fun p => 1 + z * direction p) (PEqualNP.Gct.permPoly ℂ 4) = 24 := by
  have heval : MvPolynomial.eval (fun p => 1 + z * direction p) (PEqualNP.Gct.permPoly ℂ 4)
      = (mat z).permanent := by
    simp [mat, PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]
  rw [heval]
  have twice (w : ℂ) : Complex.I*(Complex.I*w) = -w := by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  have hneg (w : ℂ) : (mat (-w)).permanent = (mat w).permanent := by
    rw [← twice, rotate_perm, rotate_perm]
  have htotal : (mat z).permanent + (mat (-z)).permanent + (mat (Complex.I*z)).permanent +
      (mat (-(Complex.I*z))).permanent = 96 := by
    simp only [by_perm, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _σ : Equiv.Perm I4, (4 : ℂ) := by
        apply Finset.sum_congr rfl
        intro σ _
        ring_nf
        simp [Complex.I_sq]
      _ = 96 := by norm_num [Fintype.card_perm, Nat.factorial]
  rw [hneg, hneg, rotate_perm] at htotal
  linear_combination htotal / 4

end PermanentLevel.FourthMoment
#print axioms PermanentLevel.FourthMoment.level
#print axioms PermanentLevel.FourthMoment.fourth_power_sum

