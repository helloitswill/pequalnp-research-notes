import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-! A complex seven-dimensional benchmark for the 5-by-5 search. -/
namespace LevelFive.Seven

open scoped BigOperators
abbrev I := Fin 5
abbrev Coeff := Fin 7 → ℂ
abbrev M := I × I → ℂ

private noncomputable def top (x : Coeff) : I → ℂ :=
  ![x 0, x 1, x 2, x 3, -(x 0+x 1+x 2+x 3)]
private noncomputable def lower (x : Coeff) : I → ℂ := ![x 4,x 5,x 6,0,0]
private noncomputable def phases : I → ℂ := ![0,1,Complex.I,-1,-Complex.I]
private noncomputable def base (x : Coeff) (i j : I) : ℂ := if i=0 then top x j else 0
private noncomputable def term (x : Coeff) (i j : I) : ℂ := phases i * lower x j
private noncomputable def mat (x : Coeff) (z : ℂ) : Matrix I I ℂ :=
  fun i j => 1 + base x i j + z * term x i j

private def rotation : Equiv.Perm I :=
  (Equiv.swap (1:I) 2 * Equiv.swap 2 3) * Equiv.swap 3 4

private lemma phases_rot (i : I) : phases (rotation i) = Complex.I * phases i := by
  fin_cases i <;> norm_num [phases, rotation, Equiv.swap_apply_def, Complex.I_mul_I]

private lemma rotation_eq_zero (i : I) : rotation i = 0 ↔ i = 0 := by
  have h0 : rotation 0 = 0 := by decide
  rw [← h0] at *
  exact rotation.injective.eq_iff

private lemma rotated (x : Coeff) (z : ℂ) :
    (mat x (Complex.I*z)).permanent = (mat x z).permanent := by
  have hm : mat x (Complex.I*z) = (mat x z).submatrix rotation id := by
    ext i j
    simp only [mat, Matrix.submatrix_apply, id_eq, base, term, phases_rot, rotation_eq_zero]
    ring
  rw [hm, Matrix.permanent_permute_cols]

private lemma phase_average (c₀ c₁ c₂ c₃ c₄ d₀ d₁ d₂ : ℂ) :
    (c₀+d₀)*(c₁+d₁)*(c₂+d₂)*c₃*c₄ +
    (c₀-d₀)*(c₁-d₁)*(c₂-d₂)*c₃*c₄ +
    (c₀+Complex.I*d₀)*(c₁+Complex.I*d₁)*(c₂+Complex.I*d₂)*c₃*c₄ +
    (c₀-Complex.I*d₀)*(c₁-Complex.I*d₁)*(c₂-Complex.I*d₂)*c₃*c₄ =
    4*(c₀*c₁*c₂*c₃*c₄) := by
  ring_nf
  simp [Complex.I_sq]

private lemma product_average (c d : I → ℂ) (hd3 : d 3 = 0) (hd4 : d 4 = 0) :
    (∏ j, (c j+1*d j)) + (∏ j, (c j+(-1)*d j)) +
      (∏ j, (c j+Complex.I*d j)) + (∏ j, (c j+(-Complex.I)*d j)) = 4 * ∏ j, (c j+0*d j) := by
  simpa only [Fin.prod_univ_five, hd3, hd4, mul_zero, neg_zero, add_zero, one_mul, neg_one_mul,
      neg_mul, zero_mul, sub_eq_add_neg, mul_assoc] using phase_average (c 0) (c 1) (c 2) (c 3) (c 4) (d 0) (d 1) (d 2)

private lemma unchanged (x : Coeff) : (mat x 1).permanent = (mat x 0).permanent := by
  have hi := rotated x 1
  have hm := rotated x Complex.I
  have hn := rotated x (-1)
  simp only [mul_one] at hi
  rw [Complex.I_mul_I] at hm
  simp only [mul_neg, mul_one] at hn
  have hsum : (mat x 1).permanent + (mat x (-1)).permanent +
      (mat x Complex.I).permanent + (mat x (-Complex.I)).permanent =
      4 * (mat x 0).permanent := by
    simp only [Matrix.permanent, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    let c := fun j : I => 1+base x (σ j) j
    let d := fun j : I => term x (σ j) j
    have hd3 : d 3 = 0 := by simp [d,term,lower]
    have hd4 : d 4 = 0 := by simp [d,term,lower]
    exact product_average c d hd3 hd4
  rw [hn,hm,hi] at hsum
  linear_combination hsum / 4

private lemma baseline (x : Coeff) : (mat x 0).permanent = 120 := by
  classical
  have hsame (j : I) : (∑ σ : Equiv.Perm I, top x (σ 0)) = ∑ σ : Equiv.Perm I, top x (σ j) := by
    simpa [Equiv.Perm.mul_apply] using
      ((Group.mulRight_bijective (Equiv.swap (0:I) j)).sum_comp
      (fun σ : Equiv.Perm I => top x (σ 0))).symm
  have hzero : ∑ σ : Equiv.Perm I, top x (σ 0) = 0 := by
    have htotal : ∑ j : I, ∑ σ : Equiv.Perm I, top x (σ j) = 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro σ _
      rw [Equiv.sum_comp σ (top x)]
      simp [Fin.sum_univ_five,top]
    simp_rw [← hsame] at htotal
    simpa using htotal
  rw [← Matrix.permanent_transpose, Matrix.permanent]
  simp [Matrix.transpose_apply,mat,base, Fin.prod_univ_five, Finset.sum_add_distrib,
    hzero, Fintype.card_perm,Nat.factorial]

noncomputable def perturb : Coeff →ₗ[ℂ] M where
  toFun x p := base x p.1 p.2 + term x p.1 p.2
  map_add' x y := by
    funext p
    obtain ⟨i,j⟩ := p
    fin_cases j <;> simp [base,term,top,lower,Pi.add_apply, ite_add_zero, mul_add] <;> split_ifs <;> ring
  map_smul' c x := by
    funext p
    obtain ⟨i,j⟩ := p
    fin_cases j <;> simp [base,term,top,lower,Pi.smul_apply,smul_eq_mul] <;> split_ifs <;> ring

private theorem perturb_inj : Function.Injective perturb := by
  intro x y h
  funext j
  fin_cases j
  all_goals first
    | simpa [perturb,base,top,term,lower,phases] using congrFun h (0,0)
    | simpa [perturb,base,top,term,lower,phases] using congrFun h (0,1)
    | simpa [perturb,base,top,term,lower,phases] using congrFun h (0,2)
    | simpa [perturb,base,top,term,lower,phases] using congrFun h (0,3)
    | simpa [perturb,base,top,term,lower,phases] using congrFun h (1,0)
    | simpa [perturb,base,top,term,lower,phases] using congrFun h (1,1)
    | simpa [perturb,base,top,term,lower,phases] using congrFun h (1,2)

private noncomputable def permEmbedding : Equiv.Perm I ≃ (I ↪ I) where
  toFun := Equiv.toEmbedding
  invFun f := f.equivOfFiniteSelfEmbedding
  left_inv _σ := Equiv.ext (fun _ => rfl)
  right_inv f := f.toEmbedding_equivOfFiniteSelfEmbedding

theorem seven_dimensional :
    ∃ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ),
      (∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1+t (i,f i))) = 120) ∧ Module.finrank ℂ L = 7 := by
  refine ⟨LinearMap.range perturb, ?_, ?_⟩
  · rintro t ⟨x,rfl⟩
    calc
      _ = (mat x 1).transpose.permanent := by
        rw [Matrix.permanent, ← permEmbedding.sum_comp]
        apply Finset.sum_congr rfl
        intro σ _
        apply Finset.prod_congr rfl
        intro i _
        change 1+(base x i (σ i) + term x i (σ i)) = 1+base x i (σ i)+1*term x i (σ i)
        ring
      _ = 120 := by rw [Matrix.permanent_transpose,unchanged,baseline]
  · rw [LinearMap.finrank_range_of_inj perturb_inj]
    simp [Coeff]

end LevelFive.Seven
#print axioms LevelFive.Seven.seven_dimensional

