import PEqualNP.Defs

namespace OppositeFaces

variable {I A B : Type*} [DecidableEq I] [Preorder A] [Preorder B] [OrderBot A] [OrderTop B]

/-- Nonconstant on the face obtained by fixing the first input block to its minimum. -/
def variesOnLeftBottom (f : A → B → Prop) : Prop :=
  (∃ b, f ⊥ b) ∧ (∃ b, ¬f ⊥ b)

/-- Nonconstant on the face obtained by fixing the second input block to its maximum. -/
def variesOnRightTop (f : A → B → Prop) : Prop :=
  (∃ a, f a ⊤) ∧ (∃ a, ¬f a ⊤)

/-- A monotone wire cannot vary on both faces that meet at bottom/top. -/
theorem excludes (f : A → B → Prop)
    (monoA : ∀ b, Monotone (fun a => f a b)) (monoB : ∀ a, Monotone (f a))
    (left : variesOnLeftBottom f) (right : variesOnRightTop f) : False := by
  obtain ⟨b, yes⟩ := left.1
  obtain ⟨a, no⟩ := right.2
  have corner : f ⊥ ⊤ := (monoB ⊥ (show b ≤ ⊤ from le_top)) yes
  exact no ((monoA ⊤ (show ⊥ ≤ a from bot_le)) corner)

/-- Lower bounds on the varying gates on these two faces can be added. -/
theorem add_face_bounds (signals : I → A → B → Prop) (s left right : Finset I)
    (insideL : left ⊆ s) (insideR : right ⊆ s)
    (monoA : ∀ i b, Monotone (fun a => signals i a b))
    (monoB : ∀ i a, Monotone (signals i a))
    (varyL : ∀ i ∈ left, variesOnLeftBottom (signals i))
    (varyR : ∀ i ∈ right, variesOnRightTop (signals i)) :
    left.card + right.card ≤ s.card := by
  have disjoint : Disjoint left right := Finset.disjoint_left.mpr
    (fun i hl hr => excludes (signals i) (monoA i) (monoB i) (varyL i hl) (varyR i hr))
  rw [← Finset.card_union_of_disjoint disjoint]
  exact Finset.card_le_card (Finset.union_subset insideL insideR)

end OppositeFaces

namespace OppositeFaces.Project

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The wire monotonicity helpers through mono2 are from the checked upstream
-- proof L_meta_1798 at project revision 056ae7099a75.
def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this


def wire {n : ℕ} (C : Circuit) (g : Fin C.gates.length) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD (n+g.val) false

theorem actual_wire_mono {n : ℕ} (C : Circuit) (mono : Monotone2 C)
    (x y : Fin n → Bool) (g : Fin C.gates.length) (le : x ≤ y) :
    wire C g x = true → wire C g y = true := by
  have legal : ∀ h ∈ C.gates, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2 := by
    intro h mem
    have both := mono h mem
    exact ⟨by simpa using both.1, both.2⟩
  apply mono2 C.gates legal (List.ofFn x) (List.ofFn y) (by simp)
  apply ofFn_mono
  intro i hx
  have h := le i
  rw [hx] at h
  cases hy : y i with
  | false => rw [hy] at h; exact (by decide : ¬ (true ≤ false)) h |>.elim
  | true => rfl

/-- Wires varying below a corner and wires varying above it occupy disjoint gate indices. -/
theorem actual_wire_face_budget {n : ℕ} (C : Circuit) (mono : Monotone2 C) (k : Fin n → Bool)
    (counted below above : Finset (Fin C.gates.length))
    (containedB : below ⊆ counted) (containedA : above ⊆ counted)
    (variesB : ∀ g ∈ below, ∃ x ≤ k, wire C g x = true)
    (variesA : ∀ g ∈ above, ∃ x, k ≤ x ∧ wire C g x = false) :
    below.card + above.card ≤ counted.card := by
  have disjoint : Disjoint below above := by
    apply Finset.disjoint_left.mpr
    intro g low high
    obtain ⟨x,hx,yes⟩ := variesB g low
    obtain ⟨y,hy,no⟩ := variesA g high
    have corner := actual_wire_mono C mono x k g hx yes
    have top := actual_wire_mono C mono k y g hy corner
    simp [no] at top
  rw [← Finset.card_union_of_disjoint disjoint]
  exact Finset.card_le_card (Finset.union_subset containedB containedA)

end OppositeFaces.Project
