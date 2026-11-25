import PlaneTests

namespace EncoderOperands1963

open PEqualNP.HeptadCover PlaneTests1963

abbrev Point := Fin 13
abbrev Signal := Finset Point → Prop

def RejectsExterior (l : Fin 13) (f : Signal) : Prop :=
  ∀ Q, IsQuadrangle singerLines3 Q → l ∈ missLines singerLines3 Q → ¬ f Q

-- Either a point is on the line, or one of the published rows witnesses both points.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem pair_rows : ∀ l a b : Fin 13,
    ((block false l).testBit a.val || (block false l).testBit b.val ||
      rows.any (fun r => (r.2.testBit l.val && r.1.testBit a.val) && r.1.testBit b.val)) = true := by
  decide +kernel

theorem exterior_pair (l a b : Fin 13) (ha : a ∉ singerLines3 l) (hb : b ∉ singerLines3 l) :
    ∃ Q, IsQuadrangle singerLines3 Q ∧ l ∈ missLines singerLines3 Q ∧ a ∈ Q ∧ b ∈ Q := by
  have h := pair_rows l a b
  simp only [block_incidence, Bool.false_eq_true, ite_false, decide_eq_false ha,
    decide_eq_false hb, Bool.false_or] at h
  obtain ⟨r, hr, hits⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hits
  obtain ⟨⟨hl, hpa⟩, hpb⟩ := hits
  have geo := of_decide_eq_true (List.all_eq_true.mp row_geometry r hr)
  refine ⟨decode r.1, geo.1, ?_, ?_, ?_⟩
  · rw [geo.2.1]
    simpa [decode] using hl
  · simpa [decode] using hpa
  · simpa [decode] using hpb

-- A conjunction that rejects all exterior rows has an operand with no exterior singleton.
theorem one_operand_on_line (l : Fin 13) (f g : Signal) (hf : Monotone f) (hg : Monotone g)
    (off : RejectsExterior l (fun Q => f Q ∧ g Q)) :
    (∀ a, f {a} → a ∈ singerLines3 l) ∨ (∀ b, g {b} → b ∈ singerLines3 l) := by
  classical
  by_cases left : ∀ a, f {a} → a ∈ singerLines3 l
  · exact Or.inl left
  · push Not at left
    obtain ⟨a, hfa, ha⟩ := left
    right
    intro b hgb
    by_contra hb
    obtain ⟨Q, hQ, hl, aq, bq⟩ := exterior_pair l a b ha hb
    exact off Q hQ hl ⟨hf (Finset.singleton_subset_iff.mpr aq) hfa,
      hg (Finset.singleton_subset_iff.mpr bq) hgb⟩

-- On one operand an exterior quadrangle is accepted even though none of its points is.
theorem nonlinear_operand (l : Fin 13) (f g : Signal) (hf : Monotone f) (hg : Monotone g)
    (off : RejectsExterior l (fun Q => f Q ∧ g Q))
    (fails_f : ¬ RejectsExterior l f) (fails_g : ¬ RejectsExterior l g) :
    ∃ Q, IsQuadrangle singerLines3 Q ∧ l ∈ missLines singerLines3 Q ∧
      ((f Q ∧ ∀ p ∈ Q, ¬ f {p}) ∨ (g Q ∧ ∀ p ∈ Q, ¬ g {p})) := by
  classical
  have witness (u : Signal) (fails : ¬ RejectsExterior l u)
      (single : ∀ p, u {p} → p ∈ singerLines3 l) :
      ∃ Q, IsQuadrangle singerLines3 Q ∧ l ∈ missLines singerLines3 Q ∧
        u Q ∧ ∀ p ∈ Q, ¬ u {p} := by
    unfold RejectsExterior at fails
    push Not at fails
    obtain ⟨Q, hQ, hl, hu⟩ := fails
    have disj : Disjoint (singerLines3 l) Q := (Finset.mem_filter.mp hl).2
    exact ⟨Q, hQ, hl, hu, fun p hp one => Finset.disjoint_left.mp disj (single p one) hp⟩
  rcases one_operand_on_line l f g hf hg off with left | right
  · obtain ⟨Q, hQ, hl, hit⟩ := witness f fails_f left
    exact ⟨Q, hQ, hl, Or.inl hit⟩
  · obtain ⟨Q, hQ, hl, hit⟩ := witness g fails_g right
    exact ⟨Q, hQ, hl, Or.inr hit⟩

#print axioms exterior_pair
#print axioms one_operand_on_line
#print axioms nonlinear_operand

end EncoderOperands1963
