import Mathlib.Logic.Function.DependsOn
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.TopForm PEqualNP.EdgeOwnership

-- The conversion of the plane tests to Singer coordinates follows zozoClaw in R_meta_1963_733.
-- One shore supplies a code separating each singleton from every avoiding test.
-- The two code lengths and the one-shore gates share a budget of size plus one.
-- This leaves at most thirty-eight one-shore gates in any candidate below sixty-four.
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_1963_627
  (extensions : ∀ (b : Bool) (S : Finset (Fin 13)) (v : Fin 13),
    1 ≤ S.card → S.card ≤ 3 → v ∉ S → (S.card = 3 → ∀ l : Fin 13, ¬ S ⊆
        (if b then Finset.univ.filter (fun j => l ∈ singerLines3 j) else singerLines3 l)) →
    ∃ Q ∈ quadrangles singerLines3,
      let T := if b then missLines singerLines3 Q else Q
      S ⊆ T ∧ v ∉ T)
  (shore : ∀ (b : Bool) (k : Nat) (B : Fin 13 → Finset (Fin k)),
    (∀ Q ∈ quadrangles singerLines3, ∀ R ∈ quadrangles singerLines3,
        let S := if b then missLines singerLines3 Q else Q
        let T := if b then missLines singerLines3 R else R
        (¬ S ⊆ T) → ¬ S.biUnion B ⊆ T.biUnion B) →
    (∀ (S : Finset (Fin 13)) (v : Fin 13), 1 ≤ S.card → S.card ≤ 3 → v ∉ S →
       (S.card = 3 → ∀ l : Fin 13, ¬ S ⊆
        (if b then Finset.univ.filter (fun j => l ∈ singerLines3 j) else singerLines3 l)) →
       ∃ i ∈ B v, ∀ u ∈ S, i ∉ B u) → 13 ≤ k)
  (frontier : ∀ C : Circuit, Monotone2 C → ReadsBack 26 C →
      RightOnIncidentPairs singerLines3 C →
      (∀ Q ∈ quadrangles singerLines3, C.eval (incidenceInput Q (missLines singerLines3 Q)) = false) →
      ∃ k : Bool → Nat, k false + k true + {j : Fin C.size | ∃ b : Bool,
          DependsOn (gateVal 26 C j.val) {i | decide (i.val < 13) = b}}.ncard ≤ C.size + 1 ∧
        ∀ b : Bool, ∃ B : Fin 13 → Finset (Fin (k b)), ∀ Q ∈ quadrangles singerLines3,
        let T := if b then missLines singerLines3 Q else Q
        ∀ v : Fin 13, v ∉ T → ∃ i ∈ B v, ∀ u ∈ T, i ∉ B u)
  (physical : ∀ C : Circuit, Monotone2 C → ReadsBack 26 C →
      RightOnIncidentPairs singerLines3 C →
      (∀ Q ∈ quadrangles singerLines3, C.eval (incidenceInput Q (missLines singerLines3 Q)) = false) →
      (∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
      2 ≤ andPairs 26 C → {j : Fin C.size | ∃ b : Bool,
          DependsOn (gateVal 26 C j.val) {i | decide (i.val < 13) = b}}.ncard ≤ 38 → 64 ≤ C.size) :
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∀ x10 ∈ x4.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x4 → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x2 x12 ∧ x12.size < x4.size := by
  intro D Correct Nested C mono back good small nested strict pairs
  have inc : ∀ p l : Fin 13, p - l ∈ D ↔ p ∈ singerLines3 l := by decide
  have pos : RightOnIncidentPairs singerLines3 C := by
    intro l p hp
    change C.eval ((List.ofFn fun u : Fin 13 => decide (u ∈ ({p} : Finset (Fin 13)))) ++
      List.ofFn fun v : Fin 13 => decide (v ∈ ({l} : Finset (Fin 13)))) = true
    simpa only [Finset.mem_singleton] using good.1 p l ((inc p l).mpr hp)
  have neg : ∀ Q ∈ quadrangles singerLines3,
      C.eval (incidenceInput Q (missLines singerLines3 Q)) = false := by
    intro Q hQ
    have eqLine (l : Fin 13) : Q ∩ singerLines3 l = Q.filter (fun p => p-l ∈ D) := by
      ext p
      simp [inc p l]
    have eqQ : Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter (fun p => p-l ∈ D)).card ≤ 2 := by
      change Q ∈ ((Finset.univ : Finset (Fin 13)).powersetCard 4).filter
        (fun A => ∀ l : Fin 13, (A ∩ singerLines3 l).card ≤ 2) at hQ
      simpa only [Finset.mem_filter, Finset.mem_powersetCard,
        Finset.subset_univ, true_and, eqLine] using hQ
    have eqMiss (l : Fin 13) : l ∈ missLines singerLines3 Q ↔ ∀ p ∈ Q, p-l ∉ D := by
      change (l ∈ (Finset.univ : Finset (Fin 13)).filter (fun j => Disjoint (singerLines3 j) Q)) ↔ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left, ← inc]
      aesop
    change C.eval ((List.ofFn fun u : Fin 13 => decide (u ∈ Q)) ++
      List.ofFn fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q)) = false
    simpa only [eqMiss] using good.2 Q eqQ.1 eqQ.2
  obtain ⟨k,hcount,code⟩ := frontier C mono back pos neg
  have hmin (b : Bool) : 13 ≤ k b := by
    obtain ⟨B,hB⟩ := code b
    apply shore b (k b) B
    · intro Q hQ R hR S T separate contains
      obtain ⟨v,hv,avoids⟩ := Finset.not_subset.mp separate
      obtain ⟨i,hi,hiT⟩ := hB R hR v avoids
      have found := contains (Finset.mem_biUnion.mpr ⟨v,hv,hi⟩)
      obtain ⟨u,hu,hu'⟩ := Finset.mem_biUnion.mp found
      exact hiT u hu hu'
    intro S v nonempty size outside arc
    obtain ⟨Q,hQ,contains,avoids⟩ := extensions b S v nonempty size outside arc
    obtain ⟨i,hi,avoidsCode⟩ := hB Q hQ v avoids
    exact ⟨i,hi,fun u hu => avoidsCode u (contains hu)⟩
  have both := physical C mono back pos neg strict pairs (by
    have hp := hmin false
    have hl := hmin true
    omega)
  omega
