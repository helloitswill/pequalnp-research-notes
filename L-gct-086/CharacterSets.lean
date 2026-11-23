import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Group.Embedding
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.ByContra

/-! A sumset estimate for character sets with no zero sum in the chosen degrees. -/
namespace PermanentLevel
namespace CharacterSets

open Finset
open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A normalized version of the Scherk–Kemperman unique-representation bound.
The hypothesis records that zero can only be written as zero plus zero. -/
theorem unique_zero_sum (A B : Finset G) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (hu : ∀ a ∈ A, ∀ b ∈ B, a + b = 0 → a = 0 ∧ b = 0) :
    A.card + B.card ≤ (A + B).card + 1 := by
  classical
  induction B using Finset.strongInductionOn generalizing A
  rename_i B ih
  by_cases only : B = {0}
  · subst B
    simp
  obtain ⟨b, hb, hb0⟩ : ∃ b ∈ B, b ≠ 0 := by
    by_contra! h
    exact only (Finset.ext fun x => by simpa using
      (show x ∈ B ↔ x = 0 from ⟨h x, fun hx => hx ▸ hB⟩))
  obtain ⟨e, he, bad⟩ : ∃ e ∈ A, e + b ∉ A := by
    by_contra! h
    have hsub : A.map (addRightEmbedding b) ⊆ A := by
      intro v hv
      obtain ⟨u, hu', rfl⟩ := Finset.mem_map.mp hv
      exact h u hu'
    have heq : A.map (addRightEmbedding b) = A :=
      Finset.eq_of_subset_of_card_le hsub (by simp)
    have hmem : 0 ∈ A.map (addRightEmbedding b) := heq.symm ▸ hA
    obtain ⟨a, ha, hab⟩ := Finset.mem_map.mp hmem
    exact hb0 (hu a ha b hb hab).2
  let T := B.map (addLeftEmbedding e)
  let B' := B.filter fun x => e + x ∈ A
  let A' := A ∪ T
  have hzB : 0 ∈ B' := by simpa [B'] using And.intro hB he
  have hzA : 0 ∈ A' := Finset.mem_union_left _ hA
  have hlt : B' ⊂ B := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro eqB
    have : b ∈ B' := eqB ▸ hb
    exact bad (Finset.mem_filter.mp this).2
  have source : ∀ a ∈ A', ∀ y ∈ B', a + y = 0 → a = 0 ∧ y = 0 := by
    intro a ha y hy hay
    obtain ⟨hyB, hey⟩ := Finset.mem_filter.mp hy
    rcases Finset.mem_union.mp ha with haA | haT
    · exact hu a haA y hyB hay
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp haT
      change (e + x) + y = 0 at hay
      have hh := hu (e+y) hey x hx (by simpa [add_assoc, add_comm, add_left_comm] using hay)
      have he0 := hu e he y hyB hh.1
      simp [he0.1, he0.2, hh.2]
  have hsum : A' + B' ⊆ A + B := by
    intro z hz
    obtain ⟨a, ha, y, hy, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨hyB, hey⟩ := Finset.mem_filter.mp hy
    rcases Finset.mem_union.mp ha with haA | haT
    · exact Finset.add_mem_add haA hyB
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp haT
      exact Finset.mem_add.mpr ⟨e+y, hey, x, hx, by simp [add_comm, add_left_comm]⟩
  have inter : B'.map (addLeftEmbedding e) = A ∩ T := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hw
      obtain ⟨hxB, hex⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_inter.mpr ⟨hex, Finset.mem_map.mpr ⟨x, hxB, rfl⟩⟩
    · intro hw
      obtain ⟨ha, ht⟩ := Finset.mem_inter.mp hw
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ht
      exact Finset.mem_map.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, ha⟩, rfl⟩
  have hcard := Finset.card_union_add_card_inter A T
  rw [← inter, Finset.card_map] at hcard
  have hsize : A'.card + B'.card = A.card + B.card := by simpa [A', T] using hcard
  have step := ih B' hlt A' hzA hzB source
  have monotone := Finset.card_le_card hsum
  omega

/-- Sums of at most k entries. Zero is present in the allowed set. -/
def sums (B : Finset G) : ℕ → Finset G
  | 0 => {0}
  | k+1 => sums B k + B

theorem zero_mem_sums (B : Finset G) (hb : 0 ∈ B) (k : ℕ) : 0 ∈ sums B k := by
  induction k with
  | zero => simp [sums]
  | succ k ih => simpa [sums] using Finset.add_mem_add ih hb

/-- If a sum of at most n allowed characters can be zero only by using zeros,
each step contributes at least the number of nonzero allowed characters. -/
theorem growth (B : Finset G) (hb : 0 ∈ B) (n : ℕ)
    (hn : ∀ k < n, ∀ a ∈ sums B k, ∀ b ∈ B, a + b = 0 → a = 0 ∧ b = 0) :
    1 + n * (B.card - 1) ≤ (sums B n).card := by
  induction n with
  | zero => simp [sums]
  | succ n ih =>
    have prev := ih (fun k hk => hn k (by omega))
    have step := unique_zero_sum (sums B n) B (zero_mem_sums B hb n) hb (hn n (by omega))
    have pos : 0 < B.card := Finset.card_pos.mpr ⟨0, hb⟩
    simp only [sums, Nat.succ_mul]
    omega

theorem finite_group_bound [Fintype G] (B : Finset G) (hb : 0 ∈ B) (n : ℕ)
    (hn : ∀ k < n, ∀ a ∈ sums B k, ∀ b ∈ B, a + b = 0 → a = 0 ∧ b = 0) :
    1 + n * (B.card - 1) ≤ Fintype.card G :=
  le_trans (growth B hb n hn) (Finset.card_le_univ _)

end CharacterSets
end PermanentLevel
#print axioms PermanentLevel.CharacterSets.finite_group_bound

