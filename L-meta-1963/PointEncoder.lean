import EncoderCount
import EncoderOperands

namespace PointEncoder1963

open PEqualNP.HeptadCover EncoderCount1963 EncoderOperands1963

-- The first thirteen wire indices are the point inputs. A later index is an
-- OR when orGate is true and an AND otherwise. A wire may be read any number of times.
structure Encoder where
  size : ℕ
  left : ℕ → ℕ
  right : ℕ → ℕ
  orGate : ℕ → Bool
  value : ℕ → Signal
  input : ∀ (p : Point) Q, value p.val Q ↔ p ∈ Q
  earlier : ∀ j, 13 ≤ j → j < 13 + size → left j < j ∧ right j < j
  evalGate : ∀ j, 13 ≤ j → j < 13 + size → ∀ Q, value j Q ↔
    if orGate j then value (left j) Q ∨ value (right j) Q
    else value (left j) Q ∧ value (right j) Q

def Encoder.orCount (C : Encoder) : ℕ :=
  ((Finset.range (13 + C.size)).filter (fun i => 13 ≤ i ∧ C.orGate i = true)).card

def Fits (C : Encoder) : Prop :=
  ∀ l : Fin 13, ∃ j < 13 + C.size, RejectsExterior l (C.value j) ∧
    ∀ p ∈ singerLines3 l, C.value j {p}

noncomputable def signature (f : Signal) : Finset Point := by
  classical
  exact Finset.univ.filter (fun p => f {p})

@[simp] private theorem mem_signature (f : Signal) (p : Point) :
    p ∈ signature f ↔ f {p} := by classical simp [signature]

private theorem monotone_wire (C : Encoder) (j : ℕ) (valid : j < 13 + C.size) :
    Monotone (C.value j) := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro A B sub active
    by_cases raw : j < 13
    · let p : Point := ⟨j,raw⟩
      exact (C.input p B).mpr (sub ((C.input p A).mp active))
    · have lo := Nat.le_of_not_gt raw
      obtain ⟨ha,hb⟩ := C.earlier j lo valid
      have left := ih (C.left j) ha (lt_trans ha valid)
      have right := ih (C.right j) hb (lt_trans hb valid)
      rw [C.evalGate j lo valid A] at active
      rw [C.evalGate j lo valid B]
      cases op : C.orGate j <;> simp [op] at active ⊢
      · exact ⟨left sub active.1, right sub active.2⟩
      · exact active.imp (left sub) (right sub)

private theorem supported (C : Encoder) {l : Fin 13} {j : ℕ} (valid : j < 13 + C.size)
    (safe : RejectsExterior l (C.value j)) : signature (C.value j) ⊆ singerLines3 l := by
  intro p hp
  by_contra outside
  obtain ⟨Q,hQ,hl,pq,_⟩ := exterior_pair l p p outside outside
  exact safe Q hQ hl (monotone_wire C j valid (Finset.singleton_subset_iff.mpr pq)
    ((mem_signature _ _).mp hp))

def HasSafeOperand (C : Encoder) : Prop :=
  ∀ l j, 13 ≤ j → j < 13 + C.size → C.orGate j = false →
    RejectsExterior l (C.value j) → 2 ≤ (signature (C.value j)).card →
    RejectsExterior l (C.value (C.left j)) ∨ RejectsExterior l (C.value (C.right j))

-- Giving each safe, multi-singleton AND a safe operand suffices for the count.
theorem count_with_safe_operand (C : Encoder) (fits : Fits C) (pass : HasSafeOperand C) :
    39 ≤ C.orCount := by
  classical
  let sig i := signature (C.value i)
  let safe l i := i < 13 + C.size ∧ RejectsExterior l (C.value i)
  let isOr i := 13 ≤ i ∧ C.orGate i = true
  have traceable (l : Fin 13) : Traceable sig (safe l) isOr := by
    intro j sj two
    obtain ⟨valid, off⟩ := sj
    have lo : 13 ≤ j := by
      by_contra! raw
      let p : Point := ⟨j,raw⟩
      have eq : sig j = {p} := by
        ext q
        change q ∈ signature (C.value p.val) ↔ q ∈ ({p} : Finset Point)
        rw [mem_signature, C.input]
        simp [eq_comm]
      simp [eq] at two
    obtain ⟨ha,hb⟩ := C.earlier j lo valid
    cases op : C.orGate j with
    | false =>
      have gate (Q) : C.value j Q ↔ C.value (C.left j) Q ∧ C.value (C.right j) Q := by
        simpa [op] using C.evalGate j lo valid Q
      left
      rcases pass l j lo valid op off two with sa | sb
      · refine ⟨C.left j, ha, ⟨lt_trans ha valid,sa⟩, ?_⟩
        intro p hp
        exact (mem_signature _ _).mpr ((gate _).mp ((mem_signature _ _).mp hp)).1
      · refine ⟨C.right j, hb, ⟨lt_trans hb valid,sb⟩, ?_⟩
        intro p hp
        exact (mem_signature _ _).mpr ((gate _).mp ((mem_signature _ _).mp hp)).2
    | true =>
      have gate (Q) : C.value j Q ↔ C.value (C.left j) Q ∨ C.value (C.right j) Q := by
        simpa [op] using C.evalGate j lo valid Q
      right
      refine ⟨⟨lo,op⟩, C.left j, C.right j, ha, hb, ⟨lt_trans ha valid,?_⟩,
        ⟨lt_trans hb valid,?_⟩, ?_⟩
      · exact fun Q hQ hl hit => off Q hQ hl ((gate Q).mpr (Or.inl hit))
      · exact fun Q hQ hl hit => off Q hQ hl ((gate Q).mpr (Or.inr hit))
      · ext p
        simpa [sig] using gate {p}
  apply count_ors singerLines3 (13 + C.size) sig safe isOr
  · decide +kernel
  · decide +kernel
  · exact fun _ _ s => supported C s.1 s.2
  · exact traceable
  · intro l
    obtain ⟨j, valid, off, active⟩ := fits l
    exact ⟨j,valid,⟨valid,off⟩,Finset.Subset.antisymm (supported C valid off)
      (fun p hp => (mem_signature _ _).mpr (active p hp))⟩

-- A smaller OR budget produces an explicit obstruction inside the point encoder.
theorem obstruction (C : Encoder) (fits : Fits C) (small : C.orCount < 39) :
    ∃ (l : Fin 13) (j : ℕ), 13 ≤ j ∧ j < 13 + C.size ∧ C.orGate j = false ∧
      RejectsExterior l (C.value j) ∧ 2 ≤ (signature (C.value j)).card ∧
      ¬ RejectsExterior l (C.value (C.left j)) ∧ ¬ RejectsExterior l (C.value (C.right j)) ∧
      ∃ Q, IsQuadrangle singerLines3 Q ∧ l ∈ missLines singerLines3 Q ∧
        ((C.value (C.left j) Q ∧ ∀ p ∈ Q, ¬ C.value (C.left j) {p}) ∨
         (C.value (C.right j) Q ∧ ∀ p ∈ Q, ¬ C.value (C.right j) {p})) := by
  classical
  have fail : ¬ HasSafeOperand C := fun pass => (Nat.not_le_of_gt small) (count_with_safe_operand C fits pass)
  unfold HasSafeOperand at fail
  push Not at fail
  obtain ⟨l,j,lo,hi,op,off,two,fl,fr⟩ := fail
  obtain ⟨ha,hb⟩ := C.earlier j lo hi
  refine ⟨l,j,lo,hi,op,off,two,fl,fr,?_⟩
  apply nonlinear_operand l _ _ (monotone_wire C _ (lt_trans ha hi)) (monotone_wire C _ (lt_trans hb hi)) _ fl fr
  intro Q hQ hl both
  apply off Q hQ hl
  exact (C.evalGate j lo hi Q).mpr (by simpa [op] using both)

inductive OrCone (C : Encoder) : ℕ → Prop where
  | input (p : Point) : OrCone C p.val
  | gate (j : ℕ) (lo : 13 ≤ j) (hi : j < 13 + C.size) (op : C.orGate j = true)
      (a : OrCone C (C.left j)) (b : OrCone C (C.right j)) : OrCone C j

private theorem singleton_in_or_cone {C : Encoder} {j : ℕ} (cone : OrCone C j) :
    ∀ Q, C.value j Q → ∃ p ∈ Q, C.value j {p} := by
  induction cone with
  | input p =>
    intro Q hit
    exact ⟨p,(C.input p Q).mp hit,(C.input p {p}).mpr (Finset.mem_singleton_self _)⟩
  | gate j lo hi op _ _ left right =>
    have gate (Q) : C.value j Q ↔ C.value (C.left j) Q ∨ C.value (C.right j) Q := by
      simpa [op] using C.evalGate j lo hi Q
    intro Q hit
    rcases (gate Q).mp hit with a | b
    · obtain ⟨p,pq,hp⟩ := left Q a
      exact ⟨p,pq,(gate {p}).mpr (Or.inl hp)⟩
    · obtain ⟨p,pq,hp⟩ := right Q b
      exact ⟨p,pq,(gate {p}).mpr (Or.inr hp)⟩

theorem no_nested_and (C : Encoder) (fits : Fits C)
    (flat : ∀ j, 13 ≤ j → j < 13 + C.size → C.orGate j = false →
      OrCone C (C.left j) ∧ OrCone C (C.right j)) : 39 ≤ C.orCount := by
  by_contra! small
  obtain ⟨_,j,lo,hi,op,_,_,_,_,Q,_,_,hit⟩ := obstruction C fits small
  obtain ⟨a,b⟩ := flat j lo hi op
  rcases hit with ⟨v,absent⟩ | ⟨v,absent⟩
  · obtain ⟨p,pq,hp⟩ := singleton_in_or_cone a Q v
    exact absent p pq hp
  · obtain ⟨p,pq,hp⟩ := singleton_in_or_cone b Q v
    exact absent p pq hp

#print axioms obstruction
#print axioms no_nested_and

end PointEncoder1963
