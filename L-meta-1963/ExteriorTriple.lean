import EncoderOperands
import PEqualNP.Outside.L_meta_782
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

namespace ExteriorTriple1963

open PEqualNP.CircuitLowerBounds PEqualNP.HeptadCover PEqualNP.MetaComplexity.LowMergeProof
open PlaneTests1963 EncoderOperands1963

private def coverTest (l : Fin 13) (s : ℕ) : Bool :=
  (List.finRange 13).any (fun p => s.testBit p.val && (block false l).testBit p.val) ||
  (rows.any (fun r => r.2.testBit l.val && subset s r.1) ||
    (List.finRange 13).any (fun m => (m != l) && subset s (block false m)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem all_triples :
    (List.finRange 13).all (fun l => (masks 13 3).all (coverTest l)) = true := by
  decide +kernel

-- Every exterior set of up to three points is inside a prescribed negative row
-- or inside the three points of a second line lying outside the first.
theorem small_set_cover (l : Fin 13) (S : Finset Point)
    (exterior : S ⊆ Finset.univ \ singerLines3 l) (small : S.card ≤ 3) :
    (∃ Q, IsQuadrangle singerLines3 Q ∧ l ∈ missLines singerLines3 Q ∧ S ⊆ Q) ∨
    (∃ m, l ≠ m ∧ S ⊆ singerLines3 m \ singerLines3 l) := by
  have room : ∀ k : Fin 13, 3 ≤ (Finset.univ \ singerLines3 k).card := by decide +kernel
  obtain ⟨T, st, avoid, card⟩ := Finset.exists_subsuperset_card_eq exterior small (room l)
  obtain ⟨a,b,c,ab,ac,bc,points⟩ := Finset.card_eq_three.mp card
  let s := bit a ||| bit b ||| bit c
  have repr : decode s = T := by simp [s, decode_or, decode_bit, points]
  have tested := List.all_eq_true.mp (List.all_eq_true.mp all_triples l (List.mem_finRange l)) s
    (generator_membership.2.2 a b c ab bc ac)
  simp only [coverTest, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at tested
  rcases tested with ⟨p,_,ps,pl⟩ | ⟨r,hr,rl,inc⟩ | ⟨m,_,different,inc⟩
  · have pt : p ∈ T := repr ▸ (by simpa [decode] using ps : p ∈ decode s)
    have onLine : p ∈ singerLines3 l := by simpa [block_incidence] using pl
    exact ((Finset.mem_sdiff.mp (avoid pt)).2 onLine).elim
  · have geometry := of_decide_eq_true (List.all_eq_true.mp row_geometry r hr)
    refine Or.inl ⟨decode r.1,geometry.1,?_,st.trans (repr ▸ subset_decode inc)⟩
    rw [geometry.2.1]
    simpa [decode] using rl
  · have ne : m ≠ l := by simpa using different
    have onLine : T ⊆ singerLines3 m := by
      have inc' := subset_decode inc
      simpa [repr, decode_block, sideLine] using inc'
    exact Or.inr ⟨m,ne.symm,fun p hp =>
      Finset.mem_sdiff.mpr ⟨onLine (st hp),(Finset.mem_sdiff.mp (exterior hp)).2⟩⟩

def value (C : Circuit) (w : ℕ) (S : Finset Point) : Bool :=
  (C.wires (List.ofFn (fun p : Point => decide (p ∈ S)))).getD w false

private theorem read_input {n : ℕ} (x : Fin n → Bool) (p : Fin n) :
    (List.ofFn x).getD p.val false = x p := by simp [List.getD, p.isLt]

private theorem value_mono (C : Circuit)
    (ops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) {A B : Finset Point} (sub : A ⊆ B) :
    value C w A = true → value C w B = true := by
  apply wires_mono C ops _ _ (by simp) _ w
  intro i active
  by_cases hi : i < 13
  · let p : Point := ⟨i,hi⟩
    rw [read_input (fun q : Point => decide (q ∈ A)) p] at active
    rw [read_input (fun q : Point => decide (q ∈ B)) p]
    exact decide_eq_true (sub (of_decide_eq_true active))
  · simp [List.getD,hi] at active

-- Specialization of the project's checked L-meta-782 with c = k = 3.
-- The circuit is the project's own Circuit, with thirteen designated output wires.
theorem accepted_collinear_triple (C : Circuit) (output : Fin 13 → ℕ)
    (gates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (positive : ∀ l, ∀ p ∈ singerLines3 l, value C (output l) {p} = true)
    (negative : ∀ l Q, IsQuadrangle singerLines3 Q → l ∈ missLines singerLines3 Q →
        value C (output l) Q = false)
    (small : C.size < 39) :
    ∃ l m : Fin 13, l ≠ m ∧ value C (output l) (singerLines3 m \ singerLines3 l) = true := by
  classical
  have mono := value_mono C (fun g hg => (gates g hg).1)
  have single (l p : Fin 13) : value C (output l) {p} = true ↔ p ∈ singerLines3 l := by
    refine ⟨?_,positive l p⟩
    intro hit
    by_contra outside
    obtain ⟨Q,hQ,hl,pq,_⟩ := exterior_pair l p p outside outside
    have enlarged := mono (output l) (Finset.singleton_subset_iff.mpr pq) hit
    rw [negative l Q hQ hl] at enlarged
    contradiction
  have sig (l : Fin 13) :
      (Finset.univ.filter (fun p : Fin 13 => (C.wires (List.ofFn (fun b : Fin 13 =>
        decide (b = p)))).getD (output l) false = true)) = singerLines3 l := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [value, Finset.mem_singleton] using single l p
  have width : ∀ l : Fin 13, (singerLines3 l).card = 4 := by decide +kernel
  by_contra none
  have off (l : Fin 13) (S : Finset Point) (size : S.card ≤ 3)
      (avoids : S ⊆ Finset.univ \ singerLines3 l) : value C (output l) S = false := by
    cases act : value C (output l) S with
    | false => rfl
    | true =>
      rcases small_set_cover l S avoids size with ⟨Q,hQ,hl,sub⟩ | ⟨m,ne,sub⟩
      · have hit := mono _ sub act
        rw [negative l Q hQ hl] at hit
        contradiction
      · exact (none ⟨l,m,ne,mono _ sub act⟩).elim
  have bound := PEqualNP.Outside.L_meta_782 13 13 3 singerLines3 C output (fun _ => 3)
    (by decide +kernel) (by intro i; rw [sig, width]; decide) gates
    (by intro i p hp; exact (single i p).mp (by simpa only [value, Finset.mem_singleton] using hp))
    (by
      intro l x size ext
      let S : Finset Point := Finset.univ.filter (fun p => x p = true)
      have hx : (fun p : Point => decide (p ∈ S)) = x := by funext p; simp [S]
      have avoids : S ⊆ Finset.univ \ singerLines3 l := by
        intro p hp
        have on : x p = true := (Finset.mem_filter.mp hp).2
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun inside => by
          rw [ext p inside] at on; contradiction⟩
      simpa only [value, hx] using off l S size avoids)
    (fun _ => le_rfl) (by intro i; rw [sig, width])
  have counted : 39 ≤ C.size := by simpa using bound
  omega

#print axioms small_set_cover
#print axioms accepted_collinear_triple

end ExteriorTriple1963
