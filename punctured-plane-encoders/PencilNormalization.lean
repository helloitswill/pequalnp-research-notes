import PencilEncoders
import PEqualNP.MetaComplexity.Helpers.Elim

namespace PuncturedPlaneEncoders

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

private def binary (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

private theorem emit_binary (op : GateOp) (m : ℕ) (ins : List Stat)
    (mono : op = GateOp.and ∨ op = GateOp.or) :
    ∀ g ∈ (simplify op m ins).1, binary g := by
  intro g hg
  rcases mono with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplify, simpAnd] at hg
    subst hg
    simp [binary]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplify, simpOr] at hg
    subst hg
    simp [binary]

private theorem pass_binary (n : ℕ) (gs : List Gate) :
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ a : List Stat × List Gate, (∀ g ∈ a.2, binary g) → ∀ g ∈ (elim n gs a).2, binary g := by
  induction gs with
  | nil => intro _ a good; exact good
  | cons g gs ih =>
    intro mono a good
    apply ih (fun g' mem => mono g' (List.mem_cons_of_mem g mem)) (elimStep n a g)
    intro g' mem
    rcases List.mem_append.mp mem with old | newGate
    · exact good g' old
    · exact emit_binary _ _ _ (mono g List.mem_cons_self) g' (by simpa using newGate)

private def initial (n : ℕ) : List Stat × List Gate :=
  (List.ofFn (fun i : Fin n => Stat.wire i.val), [])

private theorem initial_correct {n : ℕ} (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn x) (initial n) := by
  refine ⟨by simp [initial], ?_⟩
  intro i
  by_cases hi : i < n
  · simp [initial, List.getD, hi, Stat.Valid, Stat.val, wiresFrom]
  · have hs : (List.ofFn (fun a : Fin n => Stat.wire a.val)).length ≤ i := by simpa using Nat.le_of_not_gt hi
    have hx : (List.ofFn x).length ≤ i := by simpa using Nat.le_of_not_gt hi
    change ((_ : List Stat).getD i _).Valid _ ∧ ((_ : List Stat).getD i _).val _ = _
    simp only [initial]
    rw [List.getD_eq_default _ _ hs, List.getD_eq_default _ _ hx]
    exact ⟨trivial, rfl⟩

-- The same simplification preserves every nonconstant designated wire simultaneously.
theorem normalize_outputs {n m : ℕ} (C : Circuit) (o : Fin m → ℕ) (mono : Monotone2 C)
    (varies : ∀ i, ∃ x y : Fin n → Bool, (C.wires (List.ofFn x)).getD (o i) false = false ∧
      (C.wires (List.ofFn y)).getD (o i) false = true) :
    ∃ (D : Circuit) (v : Fin m → ℕ), D.size ≤ C.size ∧
      (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      ∀ i (x : Fin n → Bool), (D.wires (List.ofFn x)).getD (v i) false =
        (C.wires (List.ofFn x)).getD (o i) false := by
  classical
  let acc := elim n C.gates (initial n)
  let D : Circuit := ⟨acc.2, 0⟩
  have ops (g) (mem : g ∈ C.gates) : g.op = GateOp.and ∨ g.op = GateOp.or := (mono g mem).1
  have ok (g) (mem : g ∈ C.gates) : Ok g := by
    refine ⟨?_, (mono g mem).2⟩
    rcases ops g mem with h | h <;> simp [h]
  have val (i : Fin m) (x : Fin n → Bool) :
      (acc.1.getD (o i) (Stat.const false)).val (D.wires (List.ofFn x)) =
        (C.wires (List.ofFn x)).getD (o i) false :=
    ((inv_elim n (List.ofFn x) (by simp) C.gates (List.ofFn x) (initial n) ok (initial_correct x)).2 (o i)).2
  have hw (i : Fin m) : ∃ w, acc.1.getD (o i) (Stat.const false) = Stat.wire w := by
    cases h : acc.1.getD (o i) (Stat.const false) with
    | wire w => exact ⟨w,rfl⟩
    | const b =>
      obtain ⟨x,y,hx,hy⟩ := varies i
      have a := val i x
      have b' := val i y
      rw [h, hx] at a
      rw [h, hy] at b'
      change b = false at a
      change b = true at b'
      rw [a] at b'
      contradiction
  choose v hv using hw
  refine ⟨D,v,?_,pass_binary n C.gates ops (initial n) (by simp [initial]),?_⟩
  · simpa [D, Circuit.size, acc, initial] using elim_len n C.gates (initial n)
  · intro i x
    simpa only [hv i, Stat.val] using val i x

theorem order_three_encoder_at_most_two (C : Circuit) (o : Fin 13 → ℕ)
    (mono : Monotone2 C)
    (correct : ∀ p (x : Fin 13 → Bool), (C.wires (List.ofFn x)).getD (o p) false = true ↔
      ∃ l ∈ orderThree p, x l = true) : 62 ≤ C.size + 12 + 11 := by
  have nonempty : ∀ p, (orderThree p).Nonempty := by decide +kernel
  obtain ⟨D, v, size, ops, eq⟩ := normalize_outputs (n := 13) C o mono (by
    intro p
    refine ⟨fun _ => false, fun _ => true, ?_, ?_⟩
    · cases h : (C.wires (List.ofFn (fun _ : Fin 13 => false))).getD (o p) false with
      | false => rfl
      | true => obtain ⟨_, _, bad⟩ := (correct p _).mp h; contradiction
    · obtain ⟨l, hl⟩ := nonempty p
      exact (correct p _).mpr ⟨l, hl, rfl⟩)
  have bound := order_three_encoder D v ops (fun p x => (eq p x) ▸ correct p x)
  omega

end PuncturedPlaneEncoders
