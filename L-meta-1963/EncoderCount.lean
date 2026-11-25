import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace EncoderCount1963

-- A wire's signature is the set of point singletons on which it is true.
-- For a fixed line, a wire is safe if it rejects every exterior quadrangle.
-- At a safe wire with two or more positive singletons, an AND may be traced
-- through a safe parent. An OR uses two safe parents and unites their signatures.
abbrev Signature := ℕ → Finset (Fin 13)

def Joins (sig : Signature) (safe : ℕ → Prop) (j : ℕ) : Prop :=
  ∃ a b : ℕ, a < j ∧ b < j ∧ safe a ∧ safe b ∧ sig j = sig a ∪ sig b

def Traceable (sig : Signature) (safe isOr : ℕ → Prop) : Prop :=
  ∀ j, safe j → 2 ≤ (sig j).card →
    (∃ i < j, safe i ∧ sig j ⊆ sig i) ∨ (isOr j ∧ Joins sig safe j)

-- The first safe wire with an upward-closed property must acquire it at an OR.
private theorem first_join {sig : Signature} {safe isOr : ℕ → Prop}
    (traceable : Traceable sig safe isOr) (P : Finset (Fin 13) → Prop)
    (up : ∀ {A B}, A ⊆ B → P A → P B) (large : ∀ {A}, P A → 2 ≤ A.card)
    {j : ℕ} (sj : safe j) (pj : P (sig j)) :
    ∃ w ≤ j, safe w ∧ P (sig w) ∧ (∀ i < w, safe i → ¬ P (sig i)) ∧
      isOr w ∧ Joins sig safe w := by
  classical
  have ex : ∃ i, safe i ∧ P (sig i) := ⟨j, sj, pj⟩
  let w := Nat.find ex
  have hw : safe w ∧ P (sig w) := Nat.find_spec ex
  have first (i : ℕ) (hi : i < w) (si : safe i) (pi : P (sig i)) : False :=
    (Nat.not_lt_of_ge (Nat.find_min' ex ⟨si, pi⟩)) hi
  refine ⟨w, Nat.find_min' ex ⟨sj,pj⟩, hw.1, hw.2, first, ?_⟩
  rcases traceable w hw.1 (large hw.2) with ⟨i, hi, si, included⟩ | joined
  · exact (first i hi si (up included hw.2)).elim
  · exact joined

-- Three singletons need two distinct ORs on or before the indicated wire.
private theorem two_ors {sig : Signature} {safe isOr : ℕ → Prop}
    (h : Traceable sig safe isOr) {j : ℕ} (sj : safe j) (hj : 3 ≤ (sig j).card) :
    ∃ a b, a < b ∧ b ≤ j ∧ (safe a ∧ isOr a ∧ 2 ≤ (sig a).card) ∧
      (safe b ∧ isOr b ∧ 2 ≤ (sig b).card) := by
  obtain ⟨b, bj, sb, hb, _, ob, u, v, ub, vb, su, sv, eq⟩ :=
    first_join h (fun s => 3 ≤ s.card) (fun sub n => n.trans (Finset.card_le_card sub))
      (fun n => by omega) sj hj
  have cap := Finset.card_union_le (sig u) (sig v)
  rw [← eq] at cap
  have earlier : ∃ i < b, safe i ∧ 2 ≤ (sig i).card := by
    by_cases hu : 2 ≤ (sig u).card
    · exact ⟨u, ub, su, hu⟩
    · exact ⟨v, vb, sv, by omega⟩
  obtain ⟨i, ib, si, hi⟩ := earlier
  obtain ⟨a, ai, sa, ha, _, oa, _⟩ :=
    first_join h (fun s => 2 ≤ s.card) (fun sub n => n.trans (Finset.card_le_card sub))
      (fun n => n) si hi
  exact ⟨a, b, lt_of_le_of_lt ai ib, bj, ⟨sa, oa, ha⟩, ⟨sb, ob, by omega⟩⟩

private theorem three_ors {sig : Signature} {safe isOr : ℕ → Prop}
    (h : Traceable sig safe isOr) {j : ℕ} (sj : safe j) (hj : 4 ≤ (sig j).card) :
    ∃ a b c, a ≠ b ∧ a < c ∧ b < c ∧ c ≤ j ∧
      (safe a ∧ isOr a ∧ 2 ≤ (sig a).card) ∧
      (safe b ∧ isOr b ∧ 2 ≤ (sig b).card) ∧
      (safe c ∧ isOr c ∧ 2 ≤ (sig c).card) := by
  obtain ⟨c, cj, sc, hc, first, oc, u, v, uc, vc, su, sv, eq⟩ :=
    first_join h (fun s => 4 ≤ s.card) (fun sub n => n.trans (Finset.card_le_card sub))
      (fun n => by omega) sj hj
  by_cases prior : ∃ i < c, safe i ∧ 3 ≤ (sig i).card
  · obtain ⟨i, ic, si, hi⟩ := prior
    obtain ⟨a, b, ab, bi, oa, ob⟩ := two_ors h si hi
    exact ⟨a,b,c,ne_of_lt ab,by omega,by omega,cj,oa,ob,sc,oc,by omega⟩
  · have hu : (sig u).card < 3 := Nat.lt_of_not_ge (fun n => prior ⟨u,uc,su,n⟩)
    have hv : (sig v).card < 3 := Nat.lt_of_not_ge (fun n => prior ⟨v,vc,sv,n⟩)
    have cap := Finset.card_union_le (sig u) (sig v)
    rw [← eq] at cap
    have witness (i : ℕ) (si : safe i) (hi : 2 ≤ (sig i).card) :
        ∃ a ≤ i, safe a ∧ sig i ⊆ sig a ∧ isOr a ∧ 2 ≤ (sig a).card := by
      obtain ⟨a, ai, sa, incl, _, oa, _⟩ :=
        first_join h (fun s => sig i ⊆ s) (fun sub incl => incl.trans sub)
          (fun incl => hi.trans (Finset.card_le_card incl)) si (Finset.Subset.rfl)
      exact ⟨a,ai,sa,incl,oa,hi.trans (Finset.card_le_card incl)⟩
    obtain ⟨a, au, sa, ua, oa, ha⟩ := witness u su (by omega)
    obtain ⟨b, bv, sb, vb, ob, hb⟩ := witness v sv (by omega)
    have ab : a ≠ b := by
      rintro rfl
      have incl : sig c ⊆ sig a := eq ▸ Finset.union_subset ua vb
      exact first a (by omega) sa (hc.trans (Finset.card_le_card incl))
    exact ⟨a,b,c,ab,by omega,by omega,cj,⟨sa,oa,ha⟩,⟨sb,ob,hb⟩,sc,oc,by omega⟩

-- The hypotheses describe wires in gate order, allow arbitrary sharing, and also
-- allow raw inputs in the index range. Only OR gates are counted on the right.
theorem count_ors (lines : Fin 13 → Finset (Fin 13)) (n : ℕ)
    (sig : Signature) (safe : Fin 13 → ℕ → Prop) (isOr : ℕ → Prop) [DecidablePred isOr]
    (width : ∀ l, (lines l).card = 4)
    (meet : ∀ l k, l ≠ k → ((lines l) ∩ (lines k)).card ≤ 1)
    (contained : ∀ l i, safe l i → sig i ⊆ lines l)
    (traceable : ∀ l, Traceable sig (safe l) isOr)
    (outputs : ∀ l, ∃ j < n, safe l j ∧ sig j = lines l) :
    39 ≤ ((Finset.range n).filter isOr).card := by
  classical
  let charged (l : Fin 13) := (Finset.range n).filter
    (fun i => safe l i ∧ isOr i ∧ 2 ≤ (sig i).card)
  have cost (l : Fin 13) : 3 ≤ (charged l).card := by
    obtain ⟨j, jn, sj, out⟩ := outputs l
    obtain ⟨a,b,c,ab,ac,bc,cj,ha,hb,hc⟩ :=
      three_ors (traceable l) sj (by rw [out, width])
    have sub : {a,b,c} ⊆ charged l := by
      intro i hi
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hi :
        i = a ∨ i = b ∨ i = c) with rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ha⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hb⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hc⟩
    simpa [ab, ne_of_lt ac, ne_of_lt bc] using Finset.card_le_card sub
  have disj : ((Finset.univ : Finset (Fin 13)) : Set (Fin 13)).PairwiseDisjoint charged := by
    intro l _ k _ different
    apply Finset.disjoint_left.mpr
    intro i il ik
    have hl := (Finset.mem_filter.mp il).2
    have hk := (Finset.mem_filter.mp ik).2
    have sub : sig i ⊆ (lines l) ∩ (lines k) :=
      Finset.subset_inter (contained l i hl.1) (contained k i hk.1)
    have cap := (Finset.card_le_card sub).trans (meet l k different)
    omega
  have allOr : Finset.univ.biUnion charged ⊆ (Finset.range n).filter isOr := by
    intro i hi
    obtain ⟨l, _, il⟩ := Finset.mem_biUnion.mp hi
    have entry := Finset.mem_filter.mp il
    exact Finset.mem_filter.mpr ⟨entry.1, entry.2.2.1⟩
  calc
    39 = ∑ _l : Fin 13, (3 : ℕ) := by decide
    _ ≤ ∑ l : Fin 13, (charged l).card := Finset.sum_le_sum (fun l _ => cost l)
    _ = (Finset.univ.biUnion charged).card := (Finset.card_biUnion disj).symm
    _ ≤ _ := Finset.card_le_card allOr

#print axioms count_ors

end EncoderCount1963
