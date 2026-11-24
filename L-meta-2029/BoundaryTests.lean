import PEqualNP.Defs

/-! Exact and irredundant black-box tests for monotone predicates on finite sets. -/
namespace BoundaryTests

variable {V : Type*}

/-- Test every minimal true input and every maximal false input. -/
def boundary (P : Finset V → Prop) : Set (Finset V) :=
  {s | Minimal P s ∨ Maximal (fun t => ¬ P t) s}

/-- Agreement on the tested inputs suffices to identify the target among monotone predicates. -/
def determines (tests : Set (Finset V)) (P : Finset V → Prop) : Prop :=
  ∀ Q : Finset V → Prop, Monotone Q → (∀ s ∈ tests, Q s ↔ P s) → Q = P

theorem sufficient [Finite V] (P : Finset V → Prop) :
    determines (boundary P) P := by
  classical
  intro Q mono agree
  funext s
  apply propext
  by_cases hs : P s
  · obtain ⟨t, hts, ht⟩ := exists_minimal_le_of_wellFoundedLT P s hs
    exact iff_of_true (mono hts ((agree t (Or.inl ht)).2 ht.prop)) hs
  · obtain ⟨t, hst, ht⟩ := exists_maximal_ge_of_wellFoundedGT (fun t => ¬ P t) s hs
    exact iff_of_false (fun h => ht.prop ((agree t (Or.inr ht)).1 (mono hst h))) hs

/-- Flipping any single boundary value preserves monotonicity and leaves every other value fixed. -/
theorem flip_boundary (P : Finset V → Prop) (mono : Monotone P)
    {s : Finset V} (hs : s ∈ boundary P) :
    ∃ Q : Finset V → Prop, Monotone Q ∧ (∀ t, t ≠ s → (Q t ↔ P t)) ∧ ¬ (Q s ↔ P s) := by
  classical
  rcases hs with hmin | hmax
  · refine ⟨fun t => P t ∧ t ≠ s, ?_, ?_, ?_⟩
    · rintro x y hxy ⟨hx, hxs⟩
      refine ⟨mono hxy hx, ?_⟩
      rintro rfl
      exact hxs (le_antisymm hxy (hmin.le_of_le hx hxy))
    · intro t hne
      simp [hne]
    · simp [hmin.prop]
  · refine ⟨fun t => P t ∨ t = s, ?_, ?_, ?_⟩
    · intro x y hxy h
      rcases h with hx | rfl
      · exact Or.inl (mono hxy hx)
      · by_cases hy : P y
        · exact Or.inl hy
        · exact Or.inr (le_antisymm (hmax.2 hy hxy) hxy)
    · intro t hne
      simp [hne]
    · simp [hmax.prop]

/-- Every sufficient suite contains the entire boundary, including when additional rows are allowed. -/
theorem determines_iff [Finite V] (P : Finset V → Prop) (mono : Monotone P)
    (tests : Set (Finset V)) : determines tests P ↔ boundary P ⊆ tests := by
  classical
  constructor
  · intro determine s hs
    by_contra omitted
    obtain ⟨Q, hQ, agree, differ⟩ := flip_boundary P mono hs
    have eq := determine Q hQ (fun t ht => agree t (fun e => omitted (e ▸ ht)))
    exact differ (eq ▸ Iff.rfl)
  · intro contains Q hQ agree
    exact sufficient P Q hQ (fun s hs => agree s (contains hs))

/-- A monotone predicate is the disjunction of the conjunctions of its minimal true vertex sets. -/
theorem minterm_expansion (P : Finset V → Prop) (mono : Monotone P) (s : Finset V) :
    P s ↔ ∃ t : Finset V, Minimal P t ∧ t ⊆ s := by
  constructor
  · intro hs
    obtain ⟨t, hts, ht⟩ := exists_minimal_le_of_wellFoundedLT P s hs
    exact ⟨t, ht, hts⟩
  · rintro ⟨t, ht, hts⟩
    exact mono hts ht.prop

/-- The graph target accepts exactly the vertex sets containing both ends of an edge. -/
def hasEdge (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∃ u ∈ s, ∃ v ∈ s, G.Adj u v

theorem hasEdge_monotone (G : SimpleGraph V) : Monotone (hasEdge G) := by
  rintro s t hst ⟨u, hu, v, hv, huv⟩
  exact ⟨u, hst hu, v, hst hv, huv⟩

theorem minimal_hasEdge_iff [DecidableEq V] (G : SimpleGraph V) (s : Finset V) :
    Minimal (hasEdge G) s ↔ ∃ u v, G.Adj u v ∧ s = {u,v} := by
  constructor
  · intro hs
    obtain ⟨u, hu, v, hv, huv⟩ := hs.prop
    have sub : ({u,v} : Finset V) ⊆ s := Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv)
    have edge : hasEdge G {u,v} := ⟨u, by simp, v, by simp, huv⟩
    exact ⟨u, v, huv, le_antisymm (hs.le_of_le edge sub) sub⟩
  · rintro ⟨u, v, huv, rfl⟩
    refine ⟨⟨u, by simp, v, by simp, huv⟩, ?_⟩
    intro t ht sub
    obtain ⟨i, hi, j, hj, hij⟩ := ht
    have inc : ({i,j} : Finset V) ⊆ t := Finset.insert_subset hi (Finset.singleton_subset_iff.mpr hj)
    have eq : t = {u,v} := Finset.eq_of_subset_of_card_le sub (by
      simpa [huv.ne, hij.ne] using Finset.card_le_card inc)
    exact eq.ge

end BoundaryTests
