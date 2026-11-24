import PEqualNP.Defs

namespace MaximalCorner

def edges : List (ℕ × ℕ) := (List.range 21).flatMap (fun p =>
  [(p,21 + (p+20)%21), (p,21+p), (p,21+(p+5)%21),
   (p,21+(p+7)%21), (p,21+(p+17)%21)])

def selected : Finset (Fin 42) := {8,10,16,19,22,32,35,41}

theorem remaining : (Finset.univ \ selected).card = 34 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem independent : ∀ p q : Fin 42, p ∈ selected → q ∈ selected →
    (p.val,q.val) ∉ edges := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem maximal : ∀ p : Fin 42, p ∉ selected → ∃ q ∈ selected,
    (p.val,q.val) ∈ edges ∨ (q.val,p.val) ∈ edges := by decide +kernel

/-- Fixing all eight selected variables makes the incidence test the OR of the remaining 34. -/
theorem cofactor (x : Fin 42 → Bool) (fixed : ∀ i ∈ selected, x i = true) :
    (∃ p q : Fin 42, (p.val,q.val) ∈ edges ∧ x p = true ∧ x q = true) ↔
    ∃ p ∈ Finset.univ \ selected, x p = true := by
  constructor
  · rintro ⟨p,q,e,hp,hq⟩
    by_cases inside : p ∈ selected
    · exact ⟨q, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => independent p q inside h e⟩, hq⟩
    · exact ⟨p, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,inside⟩, hp⟩
  · rintro ⟨p,hp,on⟩
    obtain ⟨q,hq,e | e⟩ := maximal p (Finset.mem_sdiff.mp hp).2
    · exact ⟨p,q,e,on,fixed q hq⟩
    · exact ⟨q,p,e,fixed q hq,on⟩

end MaximalCorner

namespace MaximalCorner

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

noncomputable local instance : DecidableEq GateOp := Classical.decEq _

private def evalGate (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map (fun i => w.getD i false))
private def appendGate (w : List Bool) (g : Gate) := w ++ [evalGate w g]
private def zeroOn (w : List Bool) (s : Finset ℕ) := ∀ i ∈ s, w.getD i false = false
private noncomputable def orCount (gs : List Gate) : ℕ :=
  ∑ i : Fin gs.length, if (gs.get i).op = GateOp.or then 1 else 0

private theorem count_cons (g : Gate) (gs : List Gate) :
    orCount (g::gs) = (if g.op = GateOp.or then 1 else 0) + orCount gs := by
  unfold orCount
  exact Fin.sum_univ_succ (fun i : Fin (gs.length+1) => if ((g::gs).get i).op = GateOp.or then (1 : ℕ) else 0)

private theorem snoc_ne (w : List Bool) (b : Bool) {i : ℕ} (h : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases small : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left small]
  · have first : w.length ≤ i := by omega
    have both : (w ++ [b]).length ≤ i := by simp; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none both,List.getElem?_eq_none first]

private theorem snoc_at (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

private theorem gateCertificate (w : List Bool) (g : Gate)
    (valid : g.op = .and ∨ g.op = .or) (fan : g.inputs.length ≤ 2)
    (off : evalGate w g = false) :
    ∃ s : Finset ℕ, zeroOn w s ∧
      s.card ≤ 1 + (if g.op = .or then 1 else 0) ∧
      ∀ v : List Bool, zeroOn v s → evalGate v g = false := by
  rcases valid with ha | ho
  · have bad : ∃ i ∈ g.inputs, w.getD i false = false := by
      simpa [evalGate,ha,GateOp.eval,List.all_eq_false] using off
    obtain ⟨i,hi,no⟩ := bad
    refine ⟨{i}, by simpa [zeroOn] using no, by simp [ha], ?_⟩
    intro v zv
    have bad' : ∃ i ∈ g.inputs, v.getD i false = false := ⟨i,hi,zv i (by simp)⟩
    simpa [evalGate,ha,GateOp.eval,List.all_eq_false] using bad'
  · have all : ∀ i ∈ g.inputs, w.getD i false = false := by
      simpa [evalGate,ho,GateOp.eval,List.any_eq_false] using off
    refine ⟨g.inputs.toFinset, by simpa [zeroOn] using all, ?_, ?_⟩
    · simpa [ho] using (List.toFinset_card_le g.inputs).trans fan
    · intro v zv
      have all' : ∀ i ∈ g.inputs, v.getD i false = false := by simpa [zeroOn] using zv
      simpa [evalGate,ho,GateOp.eval,List.any_eq_false] using all'

private theorem backwards (gs : List Gate) (w : List Bool) (out : Finset ℕ)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (off : zeroOn (gs.foldl appendGate w) out) :
    ∃ s : Finset ℕ, zeroOn w s ∧ s.card ≤ out.card + orCount gs ∧
      ∀ v : List Bool, v.length = w.length → zeroOn v s → zeroOn (gs.foldl appendGate v) out := by
  induction gs generalizing w with
  | nil => exact ⟨out,off,by simp [orCount], fun _ _ h => h⟩
  | cons g rest ih =>
    obtain ⟨next,zn,cn,stable⟩ := ih (appendGate w g) (fun h hh => legal h (by simp [hh])) off
    have advance (v : List Bool) (len : v.length = w.length)
        (old : zeroOn v (next.erase w.length))
        (gate : w.length ∈ next → evalGate v g = false) : zeroOn (rest.foldl appendGate (appendGate v g)) out := by
      apply stable _ (by simp [appendGate,len])
      intro i hi
      by_cases eq : i = v.length
      · subst i
        change (v ++ [_]).getD v.length false = false
        rw [snoc_at]
        exact gate (len ▸ hi)
      · rw [appendGate,snoc_ne v _ eq]
        exact old i (Finset.mem_erase.mpr ⟨by omega,hi⟩)
    have prev : zeroOn w (next.erase w.length) := by
      intro i hi
      obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hi
      have keep := zn i mem
      change (w ++ [evalGate w g]).getD i false = false at keep
      rw [snoc_ne w _ ne] at keep
      exact keep
    by_cases active : w.length ∈ next
    · have gateOff : evalGate w g = false := by simpa [appendGate,snoc_at] using zn _ active
      have ⟨valid,fan⟩ := legal g (by simp)
      obtain ⟨add,za,ca,applyGate⟩ := gateCertificate w g valid fan gateOff
      refine ⟨(next.erase w.length) ∪ add, ?_, ?_, ?_⟩
      · intro i hi
        exact (Finset.mem_union.mp hi).elim (prev i) (za i)
      · have cu := Finset.card_union_le (next.erase w.length) add
        have ce := Finset.card_erase_add_one active
        rw [count_cons]
        omega
      · intro v len preserved
        exact advance v len (fun i h => preserved i (Finset.mem_union_left _ h))
          (fun _ => applyGate v (fun i h => preserved i (Finset.mem_union_right _ h)))
    · refine ⟨next.erase w.length,prev, ?_, ?_⟩
      · rw [count_cons,Finset.erase_eq_of_notMem active]
        omega
      · exact fun v len preserved => advance v len preserved (fun h => (active h).elim)

end MaximalCorner

namespace MaximalCorner

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Every correct fan-in-two monotone circuit for the posted incidence function uses at least 33 OR gates. -/
theorem count_lower_bound (C : Circuit) (mono : Monotone2 C)
    (computes : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p q : Fin 42, (p.val,q.val) ∈ edges ∧ x p = true ∧ x q = true) :
    33 ≤ {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard := by
  classical
  let base : Fin 42 → Bool := fun u => decide (u ∈ selected)
  have off : C.eval (List.ofFn base) = false := by
    apply Bool.eq_false_iff.mpr
    intro accepts
    obtain ⟨p,hp,on⟩ := (cofactor base (by simp [base])).1 ((computes base).1 accepts)
    exact (Finset.mem_sdiff.mp hp).2 (by simpa [base] using on)
  have init : zeroOn (C.gates.foldl appendGate (List.ofFn base)) {C.output} := by
    intro i hi
    obtain rfl := Finset.mem_singleton.mp hi
    exact off
  have legal : ∀ h ∈ C.gates, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2 := by
    intro h mem
    have both := mono h mem
    exact ⟨by simpa using both.1,both.2⟩
  obtain ⟨s,chosen,sz,stable⟩ := backwards C.gates (List.ofFn base) {C.output} legal init
  have included : ((Finset.univ \ selected).image Fin.val) ⊆ s := by
    intro k hk
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
    by_contra out
    let changed : Fin 42 → Bool := fun i => decide (i ∈ selected ∨ i = v)
    have on : C.eval (List.ofFn changed) = true := (computes changed).2
      ((cofactor changed (fun i hi => by simp [changed,hi])).2 ⟨v,hv,by simp [changed]⟩)
    have preserved : zeroOn (List.ofFn changed) s := by
      intro i hi
      by_cases valid : i < 42
      · have ne : (⟨i,valid⟩ : Fin 42) ≠ v := by
          rintro eq
          exact out (by simpa [←eq] using hi)
        have atI := chosen i hi
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, valid, dite_true, Option.getD_some] at atI ⊢
        simpa only [changed, base, ne, or_false] using atI
      · rw [List.getD_eq_default]
        simpa using Nat.le_of_not_gt valid
    have same := stable (List.ofFn changed) (by simp) preserved C.output (by simp)
    change C.eval (List.ofFn changed) = false at same
    exact Bool.noConfusion (on.symm.trans same)
  have count := Finset.card_le_card included
  rw [Finset.card_image_of_injective _ Fin.val_injective, remaining] at count
  simp only [Finset.card_singleton] at sz
  have val : 33 ≤ orCount C.gates := by omega
  let ids := Finset.univ.filter (fun j : Fin C.gates.length => (C.gates.get j).op = GateOp.or)
  have eq : {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or} = (ids : Set _) := by
    ext j
    simp [ids]
  rw [eq, Set.ncard_coe_finset]
  simpa only [ids, Finset.card_filter, orCount] using val

end MaximalCorner
