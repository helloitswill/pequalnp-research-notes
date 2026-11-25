import PEqualNP.Outside.L_meta_6659

namespace FanoRowRestriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_6659_aux

private def nwire (C : Circuit) := 14 + C.size
private def val (C : Circuit) (x : Fin 14 → Bool) (i : ℕ) := (C.wires (List.ofFn x)).getD i false

private theorem length_w (C : Circuit) (x : Fin 14 → Bool) :
    (C.wires (List.ofFn x)).length = nwire C := by
  change (C.gates.foldl step6659 (List.ofFn x)).length = _
  simp [foldl_len6659, nwire, Circuit.size]

private theorem input_val (C : Circuit) (x : Fin 14 → Bool) (i : Fin 14) :
    val C x i.val = x i := by
  unfold val
  change (C.gates.foldl step6659 (List.ofFn x)).getD _ false = _
  rw [foldl_getD_lt6659 C.gates _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
  exact List.getElem_ofFn (by simpa only [List.length_ofFn] using i.isLt)

private def push (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op,[a,b]⟩], nwire C⟩

@[simp] private theorem push_size (C : Circuit) (op : GateOp) (a b : ℕ) :
    (push C op a b).size = C.size + 1 := by simp [Circuit.size, push]

@[simp] private theorem push_len (C : Circuit) (op : GateOp) (a b : ℕ) :
    nwire (push C op a b) = nwire C + 1 := by simp [nwire]; omega

private theorem push_wires (C : Circuit) (x : Fin 14 → Bool) (op : GateOp) (a b : ℕ) :
    (push C op a b).wires (List.ofFn x) =
      C.wires (List.ofFn x) ++ [op.eval [val C x a, val C x b]] := by
  simp [push, Circuit.wires, List.foldl_append, val]

private theorem push_old (C : Circuit) (x : Fin 14 → Bool) (op : GateOp) (a b i : ℕ)
    (hi : i < nwire C) : val (push C op a b) x i = val C x i := by
  change ((push C op a b).wires _).getD i false = _
  rw [push_wires]
  exact List.getD_append _ _ _ _ ((length_w C x).symm ▸ hi)

private theorem push_new (C : Circuit) (x : Fin 14 → Bool) (op : GateOp) (a b : ℕ) :
    val (push C op a b) x (nwire C) = op.eval [val C x a, val C x b] := by
  change ((push C op a b).wires _).getD (nwire C) false = _
  rw [push_wires, ← length_w C x, List.getD_append_right _ _ _ _ le_rfl]
  simp

private theorem push_mono (C : Circuit) (op : GateOp) (a b : ℕ)
    (h : Monotone2 C) (g : op = GateOp.and ∨ op = GateOp.or) :
    Monotone2 (push C op a b) := by
  intro G mem
  rcases List.mem_append.mp mem with old | new₁
  · exact h G old
  · obtain rfl := List.mem_singleton.mp new₁
    exact ⟨g, by simp⟩

def point (p : Fin 7) : Fin 14 := Fin.castAdd 7 p
def line (p l : Fin 7) : Fin 14 := Fin.natAdd 7 (l - p)

def hit (p : Fin 7) (x : Fin 14 → Bool) : Prop :=
  x (point p) = true ∧ (x (line p 0) = true ∨ x (line p 1) = true ∨ x (line p 3) = true)

private theorem edge_iff (x : Fin 14 → Bool) :
    HeawoodEdge x ↔ ∃ p : Fin 7, hit p x := by
  have table : ∀ u v : Fin 14, (u.val,v.val) ∈ edgeList ↔
      ∃ p : Fin 7, u = point p ∧ (v = line p 0 ∨ v = line p 1 ∨ v = line p 3) := by
    intro u
    fin_cases u <;> decide +kernel
  constructor
  · rintro ⟨u,v,edge,hp,hl⟩
    obtain ⟨p,rfl,hv⟩ := (table u v).mp edge
    refine ⟨p,hp,?_⟩
    rcases hv with rfl | rfl | rfl <;> simp_all
  · rintro ⟨p,hp,hl⟩
    rcases hl with h | h | h
    · exact ⟨_,_,(table _ _).mpr ⟨p,rfl,Or.inl rfl⟩,hp,h⟩
    · exact ⟨_,_,(table _ _).mpr ⟨p,rfl,Or.inr (Or.inl rfl)⟩,hp,h⟩
    · exact ⟨_,_,(table _ _).mpr ⟨p,rfl,Or.inr (Or.inr rfl)⟩,hp,h⟩

private def addRow (C : Circuit) (p : Fin 7) : Circuit :=
  let a := push C .or (line p 0) (line p 1)
  let b := push a .or (nwire C) (line p 3)
  let c := push b .and (point p) (nwire a)
  push c .or C.output (nwire b)

@[simp] private theorem addRow_size (C : Circuit) (p : Fin 7) : (addRow C p).size = C.size + 4 := by
  simp [addRow, Nat.add_assoc]

private theorem addRow_mono (C : Circuit) (p : Fin 7) (h : Monotone2 C) : Monotone2 (addRow C p) :=
  push_mono _ _ _ _ (push_mono _ _ _ _ (push_mono _ _ _ _ (push_mono _ _ _ _ h (Or.inr rfl))
    (Or.inr rfl)) (Or.inl rfl)) (Or.inr rfl)

private theorem addRow_eval (C : Circuit) (p : Fin 7) (x : Fin 14 → Bool) (ho : C.output < nwire C) :
    (addRow C p).eval (List.ofFn x) = true ↔ C.eval (List.ofFn x) = true ∨ hit p x := by
  let a := push C .or (line p 0) (line p 1)
  let b := push a .or (nwire C) (line p 3)
  let c := push b .and (point p) (nwire a)
  have ha : nwire a = nwire C + 1 := push_len _ _ _ _
  have hb : nwire b = nwire a + 1 := push_len _ _ _ _
  have hc : nwire c = nwire b + 1 := push_len _ _ _ _
  have eval₁ : val a x (nwire C) = (x (line p 0) || x (line p 1)) := by
    rw [show val a x (nwire C) = _ from push_new C x _ _ _, input_val, input_val]
    simp [GateOp.eval]
  have eval₂ : val b x (nwire a) = ((x (line p 0) || x (line p 1)) || x (line p 3)) := by
    rw [show val b x (nwire a) = _ from push_new a x _ _ _, eval₁, input_val]
    simp [GateOp.eval]
  have eval₃ : val c x (nwire b) = (x (point p) && ((x (line p 0) || x (line p 1)) || x (line p 3))) := by
    rw [show val c x (nwire b) = _ from push_new b x _ _ _, eval₂, input_val]
    simp [GateOp.eval]
  have keep : val c x C.output = val C x C.output := by
    rw [show val c x C.output = _ from push_old b x _ _ _ _ (by omega),
        show val b x C.output = _ from push_old a x _ _ _ _ (by omega),
        show val a x C.output = _ from push_old C x _ _ _ _ ho]
  change val (push c .or C.output (nwire b)) x (nwire c) = true ↔ val C x C.output = true ∨ hit p x
  rw [push_new, keep, eval₃]
  simp [GateOp.eval, hit, or_assoc]


def rowIncidence (S : Finset (Fin 7)) (x : Fin 14 → Bool) : Prop :=
  ∃ p ∈ S, hit p x

private theorem output_in_range (C : Circuit) (S : Finset (Fin 7)) (nonempty : S.Nonempty)
    (spec : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ rowIncidence S x) :
    C.output < nwire C := by
  obtain ⟨p,hp⟩ := nonempty
  have on := (spec (fun _ => true)).mpr ⟨p,hp,rfl,Or.inl rfl⟩
  by_contra! tooLarge
  have hlen := length_w C (fun _ => true)
  change (C.wires (List.ofFn (fun _ : Fin 14 => true))).getD C.output false = true at on
  rw [List.getD_eq_default _ _ (by omega)] at on
  contradiction

private theorem extend_rows (C : Circuit) (S T : Finset (Fin 7)) (nonempty : S.Nonempty)
    (mono : Monotone2 C)
    (spec : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ rowIncidence S x) :
    ∃ D : Circuit, D.size = C.size + 4 * T.card ∧ Monotone2 D ∧
      ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔ rowIncidence (S ∪ T) x := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨C, by simp, mono, by simpa using spec⟩
  | @insert p T out ih =>
    obtain ⟨D, hsize, hm, correct⟩ := ih
    have live := output_in_range D (S ∪ T) (nonempty.mono Finset.subset_union_left) correct
    refine ⟨addRow D p, ?_, addRow_mono _ _ hm, ?_⟩
    · rw [addRow_size, hsize, Finset.card_insert_of_notMem out]
      omega
    · intro x
      rw [addRow_eval _ _ _ live, correct]
      simp only [rowIncidence, Finset.mem_union, Finset.mem_insert]
      constructor
      · rintro (⟨q,hq,e⟩ | h)
        · exact ⟨q,hq.imp_right Or.inr,e⟩
        · exact ⟨p,Or.inr (Or.inl rfl), h⟩
      · rintro ⟨q,hq,hit⟩
        rcases hq with h | h | h
        · exact Or.inl ⟨q,Or.inl h,hit⟩
        · exact Or.inr (h ▸ hit)
        · exact Or.inl ⟨q,Or.inr h,hit⟩

theorem row_subset_lower_bound (S : Finset (Fin 7)) (nonempty : S.Nonempty)
    (C : Circuit) (mono : Monotone2 C)
    (spec : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ rowIncidence S x) :
    4 * S.card - 1 ≤ C.size := by
  classical
  obtain ⟨D, hsize, hm, correct⟩ := extend_rows C S (Finset.univ \ S) nonempty mono spec
  have un : S ∪ (Finset.univ \ S) = Finset.univ := by ext; simp
  rw [un] at correct
  have lb := heawood_lb_27 D hm (by
    intro x
    rw [correct, edge_iff]
    simp [rowIncidence])
  have cards := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  simp only [Finset.card_univ, Fintype.card_fin] at cards
  omega

#print axioms row_subset_lower_bound

end FanoRowRestriction
