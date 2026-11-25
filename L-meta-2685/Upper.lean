import Rows
import PEqualNP.Outside.L_meta_2874

namespace FanoRowRestriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def neighbors (p : Fin 7) : Finset (Fin 7) := {0-p, 1-p, 3-p}

def rowEdges (S : Finset (Fin 7)) : Finset (Fin 7 × Fin 7) :=
  S.biUnion (fun p => ({p} : Finset (Fin 7)) ×ˢ neighbors p)

@[simp] theorem mem_rowEdges (S : Finset (Fin 7)) (p l : Fin 7) :
    (p,l) ∈ rowEdges S ↔ p ∈ S ∧ l ∈ neighbors p := by simp [rowEdges]

theorem card_rowEdges (S : Finset (Fin 7)) : (rowEdges S).card = 3 * S.card := by
  have three : ∀ p : Fin 7, (neighbors p).card = 3 := by decide +kernel
  unfold rowEdges
  rw [Finset.card_biUnion]
  · simp [three, Nat.mul_comm]
  · intro p _ q _ different
    apply Finset.disjoint_left.mpr
    rintro ⟨i,j⟩ a b
    have left : i = p := by simpa using (Finset.mem_product.mp a).1
    have right : i = q := by simpa using (Finset.mem_product.mp b).1
    exact different (left.symm.trans right)

def edgeIncidence (S : Finset (Fin 7)) (x : Fin 14 → Bool) : Prop :=
  ∃ p l : Fin 7, (p,l) ∈ rowEdges S ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true

theorem incidence_equiv (S : Finset (Fin 7)) (x : Fin 14 → Bool) :
    edgeIncidence S x ↔ rowIncidence S x := by
  constructor
  · rintro ⟨p,l,edge,hp,hl⟩
    obtain ⟨inS,mem⟩ := (mem_rowEdges _ _ _).mp edge
    refine ⟨p,inS,hp,?_⟩
    simp only [neighbors, Finset.mem_insert, Finset.mem_singleton] at mem
    rcases mem with rfl | rfl | rfl <;> simp_all [line]
  · rintro ⟨p,inS,hp,hl⟩
    rcases hl with h | h | h
    · exact ⟨p,0-p, by simp [inS, neighbors], hp, h⟩
    · exact ⟨p,1-p, by simp [inS, neighbors], hp, h⟩
    · exact ⟨p,3-p, by simp [inS, neighbors], hp, h⟩

theorem no_square (S : Finset (Fin 7)) : ∀ p q l k : Fin 7, p ≠ q → l ≠ k →
    ¬ ((p,l) ∈ rowEdges S ∧ (p,k) ∈ rowEdges S ∧ (q,l) ∈ rowEdges S ∧ (q,k) ∈ rowEdges S) := by
  have sparse : ∀ p q l k : Fin 7, p ≠ q → l ≠ k →
      ¬ (l ∈ neighbors p ∧ k ∈ neighbors p ∧ l ∈ neighbors q ∧ k ∈ neighbors q) := by decide +kernel
  intro p q l k pq lk
  rintro ⟨a,b,c,d⟩
  exact sparse p q l k pq lk ⟨((mem_rowEdges _ _ _).mp a).2, ((mem_rowEdges _ _ _).mp b).2,
    ((mem_rowEdges _ _ _).mp c).2, ((mem_rowEdges _ _ _).mp d).2⟩

def separated (D : Circuit) (P L : Finset ℕ) : Prop :=
  (∀ w ∈ P, w < 7 ∨ ∃ i < D.gates.length, w = 14 + i ∧
    (NestedCover.gateAt D i).op = GateOp.or ∧ ∀ u ∈ (NestedCover.gateAt D i).inputs, u ∈ P) ∧
  (∀ w ∈ L, (7 ≤ w ∧ w < 14) ∨ ∃ i < D.gates.length, w = 14 + i ∧
    (NestedCover.gateAt D i).op = GateOp.or ∧ ∀ u ∈ (NestedCover.gateAt D i).inputs, u ∈ L) ∧
  ∀ i < D.gates.length, (NestedCover.gateAt D i).op = GateOp.and →
    ∃ a b : ℕ, (NestedCover.gateAt D i).inputs = [a,b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))

theorem row_subset_optimum (S : Finset (Fin 7)) (nonempty : S.Nonempty) :
    ∃ (D : Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 14 D ∧
      D.size = 4 * S.card - 1 ∧
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔ edgeIncidence S x) ∧
      separated D P L := by
  obtain ⟨D,W,ao,size,correct,closed,split⟩ :=
    PEqualNP.Outside.L_meta_2874 7 7 (rowEdges S) S ∅ (by
      rintro ⟨p,l⟩ mem
      exact Or.inl ((mem_rowEdges _ _ _).mp mem).1)
  have exactEval (x : Fin 14 → Bool) : D.eval (List.ofFn x) = true ↔ edgeIncidence S x := by
    change circuitFun 14 D x = true ↔ _
    rw [correct]
    simp [edgeIncidence]
  have mono : Monotone2 D := fun g m => ⟨ao.1 g m,(ao.2.2 g m).le⟩
  have lower := row_subset_lower_bound S nonempty D mono (fun x => (exactEval x).trans (incidence_equiv S x))
  rw [card_rowEdges, Finset.card_empty] at size
  refine ⟨D,W false,W true,ao,by omega,exactEval,?_,?_,?_⟩
  · intro w mem
    obtain ⟨_, side⟩ | gate := closed false w mem
    · left
      simpa using side
    · exact Or.inr gate
  · intro w mem
    obtain ⟨bound, side⟩ | gate := closed true w mem
    · exact Or.inl ⟨by simpa using side, bound⟩
    · exact Or.inr gate
  · intro i hi hand
    obtain ⟨a,b,t,args,ha,hb⟩ := split i hi hand
    cases t with
    | false => exact ⟨a,b,args,Or.inl ⟨ha,hb⟩⟩
    | true => exact ⟨a,b,args,Or.inr ⟨ha,hb⟩⟩

#print axioms row_subset_optimum

theorem row_subset_normal_form (S : Finset (Fin 7)) (nonempty : S.Nonempty)
    (C : Circuit) (mono : Monotone2 C)
    (correct : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ edgeIncidence S x) :
    ∃ (D : Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 14 D ∧ D.size ≤ C.size ∧
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔ edgeIncidence S x) ∧ separated D P L := by
  obtain ⟨D,P,L,ao,size,eval,shape⟩ := row_subset_optimum S nonempty
  have lower := row_subset_lower_bound S nonempty C mono (fun x => (correct x).trans (incidence_equiv S x))
  exact ⟨D,P,L,ao,size ▸ lower,eval,shape⟩

#print axioms row_subset_normal_form

end FanoRowRestriction
