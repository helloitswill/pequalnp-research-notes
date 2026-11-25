import PEqualNP.Defs

namespace StarRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Wire and gate lookup lemmas from the checked PEqualNP.Outside.L_meta_2874.
private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_stepW_len (gs : List Gate) (inp : List Bool) :
    (gs.foldl stepW inp).length = inp.length + gs.length := by
  induction gs generalizing inp with
  | nil => simp
  | cons g rest ih =>
    simp [List.foldl, stepW, ih]
    omega

private lemma getD_append_left (l1 l2 : List Bool) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_append_self (l1 : List Bool) (b : Bool) :
    (l1 ++ [b]).getD l1.length false = b := by
  simp [List.getD]

private def wireVal (n : ℕ) (gs : List Gate) (z : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl stepW (List.ofFn z)).getD i false

private lemma wireVal_append_gate_lt (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool)
    (i : ℕ) (hi : i < n + gs.length) :
    wireVal n (gs ++ [g]) z i = wireVal n gs z i := by
  unfold wireVal
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl stepW (List.ofFn z)).length = n + gs.length := by
    rw [foldl_stepW_len, List.length_ofFn]
  exact getD_append_left _ _ i (by omega)

private lemma wireVal_append_gate_self (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool) :
    wireVal n (gs ++ [g]) z (n + gs.length) =
      g.op.eval (g.inputs.map (fun i => wireVal n gs z i)) := by
  unfold wireVal
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl stepW (List.ofFn z)).length = n + gs.length := by
    rw [foldl_stepW_len, List.length_ofFn]
  rw [← hlen]
  exact getD_append_self (gs.foldl stepW (List.ofFn z)) _

private def gateAtL (gs : List Gate) (j : ℕ) : Gate :=
  gs.getD j ⟨GateOp.or, []⟩

private lemma gateAtL_append_lt (gs : List Gate) (g : Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtL (gs ++ [g]) j = gateAtL gs j := by
  simp [gateAtL, List.getD, List.getElem?_append_left hj]

private lemma gateAtL_append_self (gs : List Gate) (g : Gate) :
    gateAtL (gs ++ [g]) gs.length = g := by
  simp [gateAtL, List.getD]

private theorem raw {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (v : Fin n) :
    wireVal n gs x v.val = x v := by
  induction gs using List.reverseRecOn with
  | nil => simp [wireVal, List.getD, v.isLt]
  | append_singleton gs g ih =>
    rw [wireVal_append_gate_lt n gs g x v.val (by have := v.isLt; omega), ih]

private def Good (n : ℕ) (gs : List Gate) : Prop :=
  Monotone2 ⟨gs,0⟩ ∧ ReadsBack n ⟨gs,0⟩

private theorem append_good {n : ℕ} {gs : List Gate} (good : Good n gs)
    (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) {u v : ℕ}
    (hu : u < n + gs.length) (hv : v < n + gs.length) :
    Good n (gs ++ [⟨op,[u,v]⟩]) := by
  obtain ⟨mono, back⟩ := good
  constructor
  · intro g hg
    change g ∈ gs ++ [⟨op,[u,v]⟩] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact mono g hg
    · obtain rfl := List.mem_singleton.mp hg
      rcases hop with rfl | rfl <;> simp
  · intro j hj i hi
    change j < (gs ++ [Gate.mk op [u,v]]).length at hj
    change i ∈ (gateAtL (gs ++ [⟨op,[u,v]⟩]) j).inputs at hi
    by_cases old : j < gs.length
    · rw [gateAtL_append_lt _ _ _ old] at hi
      exact back j old i hi
    · simp at hj
      have atEnd : j = gs.length := by omega
      subst j
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> assumption

/-- Append an OR of one raw input and a possibly empty list. The previous wires survive. -/
private theorem append_sum {n : ℕ} (gs : List Gate) (good : Good n gs) (b : Fin n)
    (rs : List (Fin n)) :
    ∃ (hs : List Gate) (w : ℕ), Good n hs ∧ hs.length = gs.length + rs.length ∧
      w < n + hs.length ∧ (∀ x, wireVal n hs x w = (b::rs).any x) ∧
      ∀ i < n + gs.length, ∀ x, wireVal n hs x i = wireVal n gs x i := by
  induction rs with
  | nil =>
    exact ⟨gs,b,good,by simp,by have := b.isLt; omega,fun x => by simp [raw],fun _ _ _ => rfl⟩
  | cons v rs ih =>
    obtain ⟨hs,w,hgood,hlen,hbound,hvalue,hold⟩ := ih
    let g : Gate := ⟨GateOp.or,[w,v.val]⟩
    refine ⟨hs++[g], n+hs.length, append_good hgood _ (Or.inr rfl) hbound
      (by have := v.isLt; omega), by simp [hlen]; omega, by simp, ?_, ?_⟩
    · intro x
      rw [wireVal_append_gate_self]
      simp [g, GateOp.eval, hvalue, raw, Bool.or_left_comm, Bool.or_comm]
    · intro i hi x
      rw [wireVal_append_gate_lt n hs g x i (by omega), hold i hi x]

/-- Repair the flags of one nonempty star while retaining every value already accepted by C. -/
private theorem append_star_valid (n : ℕ) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack n C)
    (valid : C.output < n + C.size) (a b : Fin n) (rs : List (Fin n)) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.output < n + D.size ∧ D.size = C.size + rs.length + 2 ∧
      ∀ x : Fin n → Bool, circuitFun n D x = (circuitFun n C x || (x a && (b::rs).any x)) := by
  obtain ⟨hs,w,hgood,hlen,hbound,hvalue,hold⟩ :=
    append_sum C.gates ⟨mono,back⟩ b rs
  change C.output < n + C.gates.length at valid
  let g : Gate := ⟨GateOp.and, [a.val,w]⟩
  let gs := hs ++ [g]
  let t : Gate := ⟨GateOp.or, [C.output,n+hs.length]⟩
  have goodg : Good n gs := append_good hgood _ (Or.inl rfl) (by have := a.isLt; omega) hbound
  have gsize : gs.length = hs.length+1 := by simp [gs]
  have goodt : Good n (gs++[t]) := append_good goodg _ (Or.inr rfl) (by omega) (by omega)
  refine ⟨⟨gs++[t], n+gs.length⟩, goodt.1, goodt.2, ?_, ?_, ?_⟩
  · simp [Circuit.size]
  · simp [Circuit.size, gsize, hlen]
  · intro x
    change wireVal n (gs++[t]) x (n+gs.length) =
      (wireVal n C.gates x C.output || (x a && (b::rs).any x))
    rw [wireVal_append_gate_self]
    simp only [t, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    change (wireVal n (hs++[g]) x C.output || wireVal n (hs++[g]) x (n+hs.length)) = _
    rw [wireVal_append_gate_lt n hs g x C.output (by omega), hold C.output valid x,
      wireVal_append_gate_self]
    simp [g, GateOp.eval, raw, hvalue]

/-- Add a nonempty star with one AND, one final OR, and one OR per further leaf. -/
theorem append_star (n : ℕ) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack n C)
    (valid : C.output < n + C.size) (a b : Fin n) (rs : List (Fin n)) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size = C.size + rs.length + 2 ∧
      ∀ x : Fin n → Bool, circuitFun n D x = (circuitFun n C x || (x a && (b::rs).any x)) := by
  obtain ⟨D,m,r,_,size,values⟩ := append_star_valid n C mono back valid a b rs
  exact ⟨D,m,r,size,values⟩

/-- Each triple specifies a center, a first leaf, and the remaining leaves of a star. -/
theorem append_stars (n : ℕ) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack n C)
    (valid : C.output < n + C.size) (S : List (Fin n × Fin n × List (Fin n))) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧
      D.size = C.size + (S.map (fun s => s.2.2.length + 2)).sum ∧
      ∀ x : Fin n → Bool, circuitFun n D x =
        (circuitFun n C x || S.any (fun s => x s.1 && (s.2.1 :: s.2.2).any x)) := by
  induction S generalizing C with
  | nil => exact ⟨C,mono,back,by simp,fun _ => by simp⟩
  | cons s S ih =>
    obtain ⟨D,m,r,v,size,values⟩ := append_star_valid n C mono back valid s.1 s.2.1 s.2.2
    obtain ⟨E,em,er,esize,evals⟩ := ih D m r v
    refine ⟨E,em,er,?_,?_⟩
    · simp only [List.map_cons, List.sum_cons]
      omega
    · intro x
      rw [evals, values]
      simp [Bool.or_assoc]

#print axioms append_star
#print axioms append_stars
end StarRepair
