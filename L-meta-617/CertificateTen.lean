import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sublists

/-!
# L-meta-617: the 3-cube edge function needs more than ten monotone gates

The final theorem, `PEqualNP.Outside.Meta617.no_cube617`, negates the posted
existence statement. The proof works on 12 positive and 6 negative input
assignments, using a 72-bit flag for each positive–negative pair. It translates
arbitrary project circuits to traces of binary AND and OR gates and checks the
width and separation conditions on every trace. At budget ten, 45 states up
to permuting the example pairs suffice to exclude all possible traces.
The concrete tables are checked in Lean with kernel reduction.

Checked against brilliant-hq/pequalnp-proofs commit
687a0753bb65edc3dae1e25dee238905156733dd with Lean 4.36.0 and the
pinned Mathlib commit fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
-/


/- Semantic traces and oriented separation of positive and negative inputs -/

namespace PEqualNP.Outside.Meta617

abbrev Bits := BitVec 72
abbrev Word := Bits × Bits
def zero : Word := (0, 0)
def one : Word := (BitVec.allOnes 72, BitVec.allOnes 72)
def goal : Word := (BitVec.allOnes 72, 0)
def meet (a b : Word) : Word := (a.1 &&& b.1, a.2 &&& b.2)
def join (a b : Word) : Word := (a.1 ||| b.1, a.2 ||| b.2)
def inv (a : Word) : Word := (~~~a.1, ~~~a.2)
def different (a : Word) : Bits := a.1 &&& ~~~a.2

inductive Makes : Word → Word → Word → Prop where
  | and (a b : Word) : Makes a b (meet a b)
  | or (a b : Word) : Makes a b (join a b)

inductive Trace : Nat → Finset Word → Prop where
  | done : Trace 0 {goal}
  | grow {n : Nat} {T : Finset Word} {a b w : Word}
      (rec : Trace n T) (use : w ∈ T) (step : Makes a b w)
      (na : w ≠ a) (nb : w ≠ b) (nz : w ≠ zero) (no : w ≠ one) :
      Trace (n+1) (insert a (insert b (T.erase w)))

theorem trace_card {n S} (h : Trace n S) : S.card ≤ n+1 := by
  induction h with
  | done => simp
  | @grow n T a b w rec use step na nb nz no ih =>
    have h₁ := Finset.card_insert_le a (insert b (T.erase w))
    have h₂ := Finset.card_insert_le b (T.erase w)
    have h₃ := Finset.card_erase_add_one use
    omega

def splitAt (i : Fin 72) (w : Word) : Prop := w.1.getLsbD i = true ∧ w.2.getLsbD i = false

theorem step_agrees {a b w} (h : Makes a b w) (i : Fin 72)
    (ha : ¬splitAt i a) (hb : ¬splitAt i b) : ¬splitAt i w := by
  unfold splitAt at *
  cases h <;> simp only [meet, join, BitVec.getLsbD_and, BitVec.getLsbD_or] at * <;>
    generalize a.1.getLsbD i = x at * <;> generalize a.2.getLsbD i = y at * <;>
    generalize b.1.getLsbD i = z at * <;> generalize b.2.getLsbD i = t at * <;>
    cases x <;> cases y <;> cases z <;> cases t <;> simp_all

theorem trace_sep {n S} (h : Trace n S) (i : Fin 72) : ∃ w ∈ S, splitAt i w := by
  induction h with
  | done =>
    refine ⟨goal, by simp, ?_⟩
    change (BitVec.allOnes 72).getLsbD i = true ∧ (0#72).getLsbD i = false
    rw [BitVec.getLsbD_allOnes, BitVec.getLsbD_zero, decide_eq_true i.isLt]
    decide
  | @grow n T a b w rec use st na nb nz no ih =>
    obtain ⟨v, hv, hs⟩ := ih
    by_cases hi : v = w
    · subst v
      by_cases ha : splitAt i a
      · exact ⟨a, by simp, ha⟩
      · by_cases hb : splitAt i b
        · exact ⟨b, by simp, hb⟩
        · exact (step_agrees st i ha hb hs).elim
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hi,hv⟩)), hs⟩

def cover : List Word → Bits
  | [] => 0
  | x :: xs => different x ||| cover xs

theorem cover_bit (xs : List Word) (i : Fin 72) :
    (cover xs).getLsbD i = true ↔ ∃ w ∈ xs, splitAt i w := by
  induction xs with
  | nil => simp [cover]
  | cons a xs ih =>
    rw [cover, BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hx : (different a).getLsbD i = true ↔ splitAt i a := by
      simp only [different, BitVec.getLsbD_and, BitVec.getLsbD_not, splitAt, i.isLt, decide_true, Bool.true_and]
      cases a.1.getLsbD i <;> cases a.2.getLsbD i <;> decide
    rw [hx]
    constructor
    · rintro (hs | ⟨v,hv,hs⟩)
      · exact ⟨a, by simp, hs⟩
      · exact ⟨v, by simp [hv], hs⟩
    · rintro ⟨v,hv,hs⟩
      rcases List.mem_cons.mp hv with rfl | hv
      · exact Or.inl hs
      · exact Or.inr ⟨v,hv,hs⟩

theorem trace_cover {n xs} (h : Trace n xs.toFinset) : cover xs = BitVec.allOnes 72 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨w, hw, hbits⟩ := trace_sep h ⟨i,hi⟩
  have hx := (cover_bit xs ⟨i,hi⟩).2 ⟨w,List.mem_toFinset.1 hw,hbits⟩
  rw [BitVec.getLsbD_allOnes, decide_eq_true hi]
  exact hx

end PEqualNP.Outside.Meta617

/- Translation from the project circuit evaluator, including its default wire values -/

namespace PEqualNP.Outside.Meta617
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def seed (ws : List Word) : Finset Word := insert zero (insert one ws.toFinset)

def rawGate (ws : List Word) (g : Gate) : Word :=
  match g.op, g.inputs with
  | .and, [] => one
  | .or, [] => zero
  | .and, [a] | .or, [a] => ws.getD a zero
  | .and, a :: b :: _ => meet (ws.getD a zero) (ws.getD b zero)
  | .or, a :: b :: _ => join (ws.getD a zero) (ws.getD b zero)
  | _, _ => zero

def rawRun (gs : List Gate) (ws : List Word) : List Word :=
  gs.foldl (fun acc g => acc ++ [rawGate acc g]) ws

theorem default_mem (ws : List Word) (i : Nat) : ws.getD i zero ∈ seed ws := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem _ _ hi]
    simp [seed, List.getElem_mem]
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [seed]

theorem raw_cases (ws : List Word) (g : Gate) :
    rawGate ws g ∈ seed ws ∨
      ∃ a ∈ seed ws, ∃ b ∈ seed ws, Makes a b (rawGate ws g) := by
  obtain ⟨o,ins⟩ := g
  cases o with
  | and =>
    cases ins with
    | nil => simp [rawGate,seed]
    | cons a is =>
      cases is with
      | nil => exact Or.inl (default_mem ws a)
      | cons b bs => exact Or.inr ⟨_,default_mem ws a,_,default_mem ws b,Makes.and _ _⟩
  | or =>
    cases ins with
    | nil => simp [rawGate,seed]
    | cons a is =>
      cases is with
      | nil => exact Or.inl (default_mem ws a)
      | cons b bs => exact Or.inr ⟨_,default_mem ws a,_,default_mem ws b,Makes.or _ _⟩
  | not => simp [rawGate,seed]
  | mod k => simp [rawGate,seed]
  | maj => simp [rawGate,seed]

theorem run_trace (gs : List Gate) (ws : List Word) (hg : goal ∈ seed (rawRun gs ws)) :
    ∃ k ≤ gs.length, ∃ S ⊆ seed ws, Trace k S := by
  induction gs generalizing ws with
  | nil => exact ⟨0,by simp,{goal},by simpa [rawRun] using hg,Trace.done⟩
  | cons g gs ih =>
    let w := rawGate ws g
    obtain ⟨k,hk,T,hT,htr⟩ := ih (ws ++ [w]) hg
    have hm : ∀ v ∈ T, v = w ∨ v ∈ seed ws := by
      intro v hv
      specialize hT hv
      simp [seed] at hT ⊢
      grind
    by_cases old : w ∈ seed ws
    · exact ⟨k,by simp; omega,T,fun v hv => (hm v hv).elim (fun e => e ▸ old) id,htr⟩
    by_cases use : w ∈ T
    · obtain h | ⟨a,ha,b,hb,st⟩ := raw_cases ws g
      · exact (old h).elim
      have na : w ≠ a := fun e => old (e ▸ ha)
      have nb : w ≠ b := fun e => old (e ▸ hb)
      have nz : w ≠ zero := by intro e; apply old; simp [e,seed]
      have no : w ≠ one := by intro e; apply old; simp [e,seed]
      refine ⟨k+1,by simp; omega,_,?_, Trace.grow htr use st na nb nz no⟩
      intro v hv
      simp only [Finset.mem_insert,Finset.mem_erase] at hv
      rcases hv with rfl | rfl | ⟨hne, hv⟩
      · exact ha
      · exact hb
      · exact (hm v hv).resolve_left hne
    · exact ⟨k,by simp; omega,T,fun v hv => (hm v hv).resolve_left (fun e => use (e ▸ hv)),htr⟩

def see (side : Bool) (i : Fin 72) (w : Word) : Bool :=
  if side then w.1.getLsbD i else w.2.getLsbD i

theorem see_zero (side : Bool) (i : Fin 72) : see side i zero = false := by
  cases side <;> simp [see,zero]
theorem see_one (side : Bool) (i : Fin 72) : see side i one = true := by
  cases side <;> change (BitVec.allOnes 72).getLsbD i = true <;> rw [BitVec.getLsbD_allOnes, decide_eq_true i.isLt]
theorem see_meet (side : Bool) (i : Fin 72) (a b : Word) :
    see side i (meet a b) = (see side i a && see side i b) := by
  cases side <;> simp [see,meet]
theorem see_join (side : Bool) (i : Fin 72) (a b : Word) :
    see side i (join a b) = (see side i a || see side i b) := by
  cases side <;> simp [see,join]
theorem see_inv (side : Bool) (i : Fin 72) (a : Word) :
    see side i (inv a) = !see side i a := by
  cases side <;> simp [see,inv,i.isLt]

theorem see_getD (side : Bool) (i : Fin 72) (ws : List Word) (j : Nat) :
    (ws.map (see side i)).getD j false = see side i (ws.getD j zero) := by
  by_cases h : j < ws.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega),see_zero]

theorem see_option (side : Bool) (i : Fin 72) (o : Option Word) :
    (o.map (see side i)).getD false = see side i (o.getD zero) := by
  cases o <;> simp [see_zero]

theorem see_gate (side : Bool) (i : Fin 72) (ws : List Word) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    g.op.eval (g.inputs.map (fun j => (ws.map (see side i)).getD j false)) = see side i (rawGate ws g) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨hop,hlen⟩ := hg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨a,(_ | ⟨b,(_ | ⟨c,cs⟩)⟩)⟩ <;>
    simp_all [GateOp.eval,rawGate,see_option,see_zero,see_one,see_meet,see_join,see_inv]

theorem see_run (side : Bool) (i : Fin 72) (ws : List Word) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun j => v.getD j false)]) (ws.map (see side i)) =
      (rawRun gs ws).map (see side i) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons, List.mem_cons] at *
    rw [see_gate side i ws g (hg g (Or.inl rfl))]
    simpa [rawRun] using ih (ws ++ [rawGate ws g]) (fun v hv => hg v (Or.inr hv))

end PEqualNP.Outside.Meta617

/- Exhaustive trace search with explicit sharing and last-use choices -/

namespace PEqualNP.Outside.Meta617

def keepList (xs : List Word) (a b : Word) (ka kb : Bool) : List Word :=
  xs.filter fun v => decide ((v ≠ a ∧ v ≠ b) ∨ (v = a ∧ ka = true) ∨ (v = b ∧ kb = true))

def alternatives (a b : Word) : List Word :=
  [meet a b, join a b]

def key (a : Word) : Nat := a.1.toNat * 2^72 + a.2.toNat

def flags : List (Bool × Bool) := [(false,false),(true,false),(false,true),(true,true)]

def possible : Nat → List Word → Bool
  | 0, xs => xs.contains goal
  | r+1, xs =>
    xs.contains goal ||
    (decide (xs.length ≤ r+2) && decide (cover xs = BitVec.allOnes 72) &&
      xs.any fun a => xs.any fun b => decide (key a ≤ key b) &&
        (alternatives a b).any fun w =>
          !xs.contains w && decide (w ≠ zero) && decide (w ≠ one) &&
          flags.any fun p => possible r (w :: keepList xs a b p.1 p.2))

theorem meet_comm (a b : Word) : meet a b = meet b a := by simp [meet,BitVec.and_comm]
theorem join_comm (a b : Word) : join a b = join b a := by simp [join,BitVec.or_comm]

theorem makes_swap {a b w} (h : Makes a b w) : Makes b a w := by
  cases h with
  | and => rw [meet_comm]; exact Makes.and _ _
  | or => rw [join_comm]; exact Makes.or _ _

theorem makes_alt {a b w} (h : Makes a b w) (na : w ≠ a) :
    w ∈ alternatives a b := by
  cases h <;> simp [alternatives]

theorem step_child (xs : List Word) {a b w : Word} (T : Finset Word)
    (hxs : xs.toFinset = insert a (insert b (T.erase w))) (hw : w ∈ T)
    (ha : w ≠ a) (hb : w ≠ b) :
    (w :: keepList xs a b (decide (a ∈ T)) (decide (b ∈ T))).toFinset = T := by
  ext v
  simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, keepList, List.mem_filter,
    decide_eq_true_eq]
  have hv : v ∈ xs ↔ v = a ∨ v = b ∨ (v ≠ w ∧ v ∈ T) := by
    rw [← List.mem_toFinset, hxs]
    simp
  rw [hv]
  by_cases e₀ : v = w <;> by_cases e₁ : v = a <;> by_cases e₂ : v = b <;> grind

theorem try_step {r n : Nat} {T : Finset Word} {a b w : Word} {xs : List Word} (htr : Trace n T) (hw : w ∈ T)
    (st : Makes a b w) (na : w ≠ a) (nb : w ≠ b) (nz : w ≠ zero) (no : w ≠ one)
    (hxs : xs.toFinset = insert a (insert b (T.erase w))) (hnod : xs.Nodup)
    (hle : key a ≤ key b) (hn : n ≤ r)
    (ih : ∀ {k : Nat} {ys : List Word}, Trace k ys.toFinset → ys.Nodup → k ≤ r → possible r ys = true) :
    possible (r+1) xs = true := by
  have hbefore : Trace (n+1) xs.toFinset := by rw [hxs]; exact Trace.grow htr hw st na nb nz no
  have hc := trace_card hbefore
  have hc' : xs.length ≤ r+2 := by
    rw [List.toFinset_card_of_nodup hnod] at hc
    omega
  have hwa : w ∉ xs := by
    rw [← List.mem_toFinset, hxs]
    simp [na,nb]
  have ham : a ∈ xs := by rw [← List.mem_toFinset, hxs]; simp
  have hbm : b ∈ xs := by rw [← List.mem_toFinset, hxs]; simp
  let p : Bool × Bool := (decide (a ∈ T), decide (b ∈ T))
  have hp : p ∈ flags := by
    dsimp [p,flags]
    by_cases ea : a ∈ T <;> by_cases eb : b ∈ T <;> simp [ea,eb]
  let ys := w :: keepList xs a b p.1 p.2
  have hys : ys.toFinset = T := step_child xs T hxs hw na nb
  have hyd : ys.Nodup := by
    apply List.nodup_cons.mpr
    exact ⟨fun h => hwa (List.mem_filter.mp h).1, hnod.filter _⟩
  have hs := ih (show Trace n ys.toFinset by rw [hys]; exact htr) hyd hn
  simp only [possible, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  right
  refine ⟨⟨hc', trace_cover hbefore⟩, a, ham, b, hbm, hle, w, makes_alt st na, ?_⟩
  simpa [hwa,nz,no] using (show ∃ q ∈ flags, possible r (w :: keepList xs a b q.1 q.2) = true from ⟨p,hp,hs⟩)

theorem trace_possible (r : Nat) {n : Nat} {xs : List Word} (h : Trace n xs.toFinset)
    (hnod : xs.Nodup) (hn : n ≤ r) : possible r xs = true := by
  induction r generalizing xs n with
  | zero =>
    have hn0 : n = 0 := by omega
    subst n
    generalize he : xs.toFinset = S at h
    cases h
    simpa [possible] using (show goal ∈ xs by rw [← List.mem_toFinset, he]; simp)
  | succ r ih =>
    generalize he : xs.toFinset = S at h
    cases h with
    | done =>
      have hm : goal ∈ xs := by rw [← List.mem_toFinset, he]; simp
      simp [possible, hm]
    | @grow k T a b w rec hw st na nb nz no =>
      have hk : k ≤ r := by omega
      by_cases hle : key a ≤ key b
      · exact try_step rec hw st na nb nz no he hnod hle hk (@ih)
      · have hle' : key b ≤ key a := by omega
        have he' : xs.toFinset = insert b (insert a (T.erase w)) := by
          simpa [Finset.insert_comm] using he
        exact try_step rec hw (makes_swap st) nb na nz no he' hnod hle' hk (@ih)

end PEqualNP.Outside.Meta617

/- The cube and its 72 ordered pairs of required examples -/

namespace PEqualNP.Outside.Meta617
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def initial : List Word := [
  (262143, 1798996755378912462360),
  (1073479743, 2698495133068368693540),
  (4396972773312, 2548578736786792655010),
  (277144592449536, 674623783267092173385),
  (1152640029630394368, 2473620538646004635745),
  (72651787714821095424, 749581981407880192650),
  (4649714418010231406592, 899498377689456231180),
  (4721213838441968566272, 3597993510757824924720)]

def edgeFn (x : Fin 8 → Bool) : Prop :=
  ∃ u v : Fin 8, (u.val, v.val) ∈
    ([(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)] : List (ℕ × ℕ))
    ∧ x u = true ∧ x v = true

def input (s : Bool) (i : Fin 72) (j : Fin 8) : Bool := see s i (initial.getD j zero)

private theorem target_rows : ∀ (s : Bool) (i : Fin 72), edgeFn (input s i) ↔ see s i goal = true := by
  unfold edgeFn
  decide

private theorem ofFn_input (s : Bool) (i : Fin 72) :
    List.ofFn (input s i) = initial.map (see s i) := by rfl

theorem output_goal (C : Circuit) (hf : Monotone2 C) (he : ∀ x, C.eval (List.ofFn x) = true ↔ edgeFn x) :
    (rawRun C.gates initial).getD C.output zero = goal := by
  have hb (s : Bool) (i : Fin 72) :
      see s i ((rawRun C.gates initial).getD C.output zero) = see s i goal := by
    have hh := he (input s i)
    rw [ofFn_input, Circuit.eval, Circuit.wires, see_run s i initial C.gates hf, see_getD,
      target_rows] at hh
    simpa using hh
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact hb true ⟨i,hi⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact hb false ⟨i,hi⟩

end PEqualNP.Outside.Meta617

/- Eliminating constant and redundant gate inputs from a trace -/

namespace PEqualNP.Outside.Meta617

private theorem meet_one (x : Word) : meet one x = x := by
  apply Prod.ext <;> exact BitVec.allOnes_and
private theorem one_meet (x : Word) : meet x one = x := by
  apply Prod.ext <;> exact BitVec.and_allOnes
private theorem join_one (x : Word) : join one x = one := by
  apply Prod.ext <;> exact BitVec.allOnes_or
private theorem one_join (x : Word) : join x one = one := by
  apply Prod.ext <;> exact BitVec.or_allOnes

private theorem source_left {a b w} (h : Makes a b w)
    (na : w ≠ a) (nb : w ≠ b) : a ≠ zero ∧ a ≠ one := by
  cases h with
  | and =>
    constructor
    · rintro rfl; exact na (by simp [meet,zero])
    · rintro rfl; exact nb (meet_one _)
  | or =>
    constructor
    · rintro rfl; exact nb (by simp [join,zero])
    · rintro rfl; exact na (join_one _)

private theorem source_right {a b w} (h : Makes a b w)
    (na : w ≠ a) (nb : w ≠ b) : b ≠ zero ∧ b ≠ one := by
  cases h with
  | and =>
    constructor
    · rintro rfl; exact nb (by simp [meet,zero])
    · rintro rfl; exact na (one_meet _)
  | or =>
    constructor
    · rintro rfl; exact na (by simp [join,zero])
    · rintro rfl; exact nb (one_join _)

theorem trace_no_constants {n S} (h : Trace n S) : zero ∉ S ∧ one ∉ S := by
  induction h with
  | done => decide
  | @grow n T a b w rec use st na nb nz no ih =>
    obtain ⟨ha, ha'⟩ := source_left st na nb
    obtain ⟨hb, hb'⟩ := source_right st na nb
    simp [Ne.symm ha, Ne.symm hb, Ne.symm ha', Ne.symm hb', ih.1, ih.2]

end PEqualNP.Outside.Meta617

/- The certificate for all one-gate continuations of a state -/

namespace PEqualNP.Outside.Meta617

def quit (r : Nat) (xs : List Word) : Bool :=
  !(xs.contains goal) && (r == 0 || decide (r+1 < xs.length) || !(cover xs == BitVec.allOnes 72))

theorem quit_false (r : Nat) (xs : List Word) (h : quit r xs = true) : possible r xs = false := by
  cases r with
  | zero => simpa [quit,possible] using h
  | succ r =>
    have hpos : (r + 1 == 0) = false := by simp
    simp only [quit, hpos, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
      Bool.or_eq_true, decide_eq_true_eq, beq_eq_false_iff_ne] at h
    obtain ⟨hn,hv⟩ := h
    rw [possible,hn,Bool.false_or]
    rcases hv with e|e
    · have hv : decide (xs.length ≤ r+2) = false := decide_eq_false (by omega)
      rw [hv,Bool.false_and,Bool.false_and]
    · have hv : decide (cover xs = BitVec.allOnes 72) = false := decide_eq_false e
      rw [hv,Bool.and_false,Bool.false_and]

def approved (r : Nat) (tab : List (List Word)) (xs : List Word) : Bool :=
  quit r xs || tab.contains xs

def stepCheck (r : Nat) (xs : List Word) (tab : List (List Word)) : Bool :=
  !(xs.contains goal) &&
  xs.all fun a => xs.all fun b => !(decide (key a ≤ key b)) ||
    (alternatives a b).all fun w =>
      xs.contains w || decide (w = zero) || decide (w = one) ||
        flags.all fun p => approved r tab (w :: keepList xs a b p.1 p.2)

end PEqualNP.Outside.Meta617

/- Soundness of the one-step certificate -/

namespace PEqualNP.Outside.Meta617

def Viable (r : Nat) (xs : List Word) : Prop :=
  ∃ k ≤ r, Trace k xs.toFinset

theorem viable_not_quit {r xs} (hd : xs.Nodup) (hv : Viable r xs) : quit r xs ≠ true := by
  rintro hq
  obtain ⟨k, hk, ht⟩ := hv
  exact Bool.false_ne_true ((quit_false r xs hq).symm.trans (trace_possible r ht hd hk))

private theorem traceCloseStep {r n : Nat} {T : Finset Word} {a b w : Word} {xs : List Word}
    (htr : Trace n T) (hw : w ∈ T) (st : Makes a b w)
    (na : w ≠ a) (nb : w ≠ b) (nz : w ≠ zero) (no : w ≠ one)
    (hxs : xs.toFinset = insert a (insert b (T.erase w))) (hd : xs.Nodup)
    (hle : key a ≤ key b) (hn : n ≤ r) (tab : List (List Word))
    (hc : stepCheck r xs tab = true) (hs : ∀ v ∈ tab, ¬ Viable r v) : False := by
  have hwa : w ∉ xs := by rw [← List.mem_toFinset, hxs]; simp [na,nb]
  have ham : a ∈ xs := by rw [← List.mem_toFinset, hxs]; simp
  have hbm : b ∈ xs := by rw [← List.mem_toFinset, hxs]; simp
  let p : Bool × Bool := (decide (a ∈ T), decide (b ∈ T))
  have hp : p ∈ flags := by
    dsimp [p,flags]
    by_cases ea : a ∈ T <;> by_cases eb : b ∈ T <;> simp [ea,eb]
  let ys := w :: keepList xs a b p.1 p.2
  have hys : ys.toFinset = T := step_child xs T hxs hw na nb
  have hyd : ys.Nodup := by
    apply List.nodup_cons.mpr
    exact ⟨fun h => hwa (List.mem_filter.mp h).1, hd.filter _⟩
  have hv : Viable r ys := ⟨n, hn, hys.symm ▸ htr⟩
  simp only [stepCheck, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, List.contains_iff_mem] at hc
  rcases hc.2 a ham b hbm with hbad|hstep
  · exact of_decide_eq_false hbad hle
  rcases hstep w (makes_alt st na) with ((hx|hz)|ho)|hflag
  · exact hwa hx
  · exact nz hz
  · exact no ho
  have hh : approved r tab ys = true := hflag p hp
  simp only [approved, Bool.or_eq_true, List.contains_iff_mem] at hh
  rcases hh with hquit|htab
  · exact viable_not_quit hyd hv hquit
  · exact hs ys htab hv

theorem trace_close {r : Nat} {xs : List Word} (tab : List (List Word))
    (hc : stepCheck r xs tab = true) (hs : ∀ v ∈ tab, ¬ Viable r v)
    (hd : xs.Nodup) : ¬ Viable (r+1) xs := by
  rintro ⟨k, hk, ht⟩
  generalize he : xs.toFinset = S at ht
  cases ht with
  | done =>
    have hg : goal ∈ xs := by rw [← List.mem_toFinset, he]; simp
    simp only [stepCheck, Bool.and_eq_true, Bool.not_eq_true'] at hc
    have hx := hc.1
    simp [hg] at hx
  | @grow n T a b w rec hw st na nb nz no =>
    have hn : n ≤ r := by omega
    by_cases hle : key a ≤ key b
    · exact traceCloseStep rec hw st na nb nz no he hd hle hn tab hc hs
    · have hle' : key b ≤ key a := by omega
      have he' : xs.toFinset = insert b (insert a (T.erase w)) := by
        simpa [Finset.insert_comm] using he
      exact traceCloseStep rec hw (makes_swap st) nb na nz no he' hd hle' hn tab hc hs

end PEqualNP.Outside.Meta617

/- A monotone circuit of bounded size yields a viable initial trace -/

namespace PEqualNP.Outside.Meta617
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem traceInitialFull : ∀ ys ∈ initial.sublists,
    cover ys = BitVec.allOnes 72 → ys = initial := by
  have hh : initial.sublists.all
      (fun ys => !(cover ys == BitVec.allOnes 72) || ys == initial) = true := by decide +kernel
  intro ys hy hc
  simpa [hc] using (List.all_eq_true.mp hh ys hy)

theorem small_implies_viable {r : Nat} {C : Circuit} (hf : Monotone2 C) (hlen : C.size ≤ r)
    (he : ∀ x, C.eval (List.ofFn x) = true ↔ edgeFn x) : Viable r initial := by
  have hy := default_mem (rawRun C.gates initial) C.output
  rw [output_goal C hf he] at hy
  obtain ⟨k,hk,S,hS,ht⟩ := run_trace C.gates initial hy
  obtain ⟨hz,hu⟩ := trace_no_constants ht
  let ys := initial.filter fun v => decide (v ∈ S)
  have heq : ys.toFinset = S := by
    ext v
    simp only [ys,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    constructor
    · exact And.right
    · intro hv
      refine ⟨?_,hv⟩
      have hp := hS hv
      simp only [seed,Finset.mem_insert,List.mem_toFinset] at hp
      rcases hp with e|e|e
      · exact (hz (e ▸ hv)).elim
      · exact (hu (e ▸ hv)).elim
      · exact e
  have ht' : Trace k ys.toFinset := by rw [heq]; exact ht
  have hi := traceInitialFull ys (List.mem_sublists.2 List.filter_sublist) (trace_cover ht')
  rw [hi] at ht'
  refine ⟨k, ?_, ht'⟩
  change C.gates.length ≤ r at hlen
  omega

end PEqualNP.Outside.Meta617

/- Trace invariance under permutations of example pairs -/

namespace PEqualNP.Outside.Meta617

def relBits (e : Fin 72 → Fin 72) (b : Bits) : Bits :=
  (BitVec.ofBoolListLE (List.ofFn fun i => b.getLsbD (e i))).cast (by simp)

@[simp] theorem relBits_at (e : Fin 72 → Fin 72) (b : Bits) (i : Fin 72) :
    (relBits e b).getLsbD i = b.getLsbD (e i) := by
  simp only [relBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem]
  · rw [List.getElem_ofFn]
  · simp only [List.length_ofFn]; exact i.isLt

private theorem bext (a b : Bits) (h : ∀ i : Fin 72, a.getLsbD i = b.getLsbD i) : a = b :=
  BitVec.eq_of_getLsbD_eq (fun i hi => h ⟨i, hi⟩)

theorem relBits_injective (e : Fin 72 → Fin 72) (he : Function.Surjective e) :
    Function.Injective (relBits e) := by
  intro a b ab
  apply bext
  intro i
  obtain ⟨j, rfl⟩ := he i
  have h := congrArg (fun v : Bits => v.getLsbD j) ab
  exact (relBits_at e a j).symm.trans (h.trans (relBits_at e b j))

@[simp] theorem relBits_zero (e : Fin 72 → Fin 72) : relBits e 0 = 0 := by
  apply bext
  intro i
  rw [relBits_at]
  change (0#72).getLsbD (e i) = (0#72).getLsbD i
  simp only [BitVec.getLsbD_zero]

@[simp] theorem relBits_ones (e : Fin 72 → Fin 72) :
    relBits e (BitVec.allOnes 72) = BitVec.allOnes 72 := by
  apply bext
  intro i
  rw [relBits_at, BitVec.getLsbD_allOnes, BitVec.getLsbD_allOnes]
  simp [i.isLt, (e i).isLt]

@[simp] theorem relBits_and (e : Fin 72 → Fin 72) (a b : Bits) :
    relBits e (a &&& b) = relBits e a &&& relBits e b := by
  apply bext
  intro i
  simp only [relBits_at, BitVec.getLsbD_and]

@[simp] theorem relBits_or (e : Fin 72 → Fin 72) (a b : Bits) :
    relBits e (a ||| b) = relBits e a ||| relBits e b := by
  apply bext
  intro i
  simp only [relBits_at, BitVec.getLsbD_or]

def relWord (e : Fin 72 → Fin 72) (w : Word) : Word := (relBits e w.1, relBits e w.2)

theorem relWord_injective (e : Fin 72 → Fin 72) (he : Function.Surjective e) :
    Function.Injective (relWord e) := by
  intro a b hab
  exact Prod.ext (relBits_injective e he (congrArg Prod.fst hab))
    (relBits_injective e he (congrArg Prod.snd hab))

@[simp] theorem relWord_goal (e : Fin 72 → Fin 72) : relWord e goal = goal := by exact Prod.ext (relBits_ones e) (relBits_zero e)
@[simp] theorem relWord_zero (e : Fin 72 → Fin 72) : relWord e zero = zero := by exact Prod.ext (relBits_zero e) (relBits_zero e)
@[simp] theorem relWord_one (e : Fin 72 → Fin 72) : relWord e one = one := by exact Prod.ext (relBits_ones e) (relBits_ones e)
@[simp] theorem relWord_meet (e : Fin 72 → Fin 72) (a b : Word) :
    relWord e (meet a b) = meet (relWord e a) (relWord e b) := by simp [relWord, meet]
@[simp] theorem relWord_join (e : Fin 72 → Fin 72) (a b : Word) :
    relWord e (join a b) = join (relWord e a) (relWord e b) := by simp [relWord, join]

theorem Makes.relabel (e : Fin 72 → Fin 72) {a b w : Word} (h : Makes a b w) :
    Makes (relWord e a) (relWord e b) (relWord e w) := by
  cases h with
  | and => rw [relWord_meet]; constructor
  | or => rw [relWord_join]; constructor

theorem Trace.relabel (e : Fin 72 → Fin 72) (he : Function.Surjective e)
    {n : Nat} {S : Finset Word} (h : Trace n S) : Trace n (S.image (relWord e)) := by
  have hinj := relWord_injective e he
  induction h with
  | done => simpa using Trace.done
  | @grow n T a b w rec use step na nb nz no ih =>
    have nz' : relWord e w ≠ zero := fun h => nz (hinj (h.trans (relWord_zero e).symm))
    have no' : relWord e w ≠ one := fun h => no (hinj (h.trans (relWord_one e).symm))
    rw [Finset.image_insert, Finset.image_insert, Finset.image_erase hinj]
    exact Trace.grow ih (Finset.mem_image_of_mem _ use) (step.relabel e)
      (fun h => na (hinj h)) (fun h => nb (hinj h)) nz' no'

end PEqualNP.Outside.Meta617

/- Transporting excluded states along a relabeling -/

namespace PEqualNP.Outside.Meta617

theorem not_viable_transport {r : Nat} {xs ys : List Word} (e : Fin 72 → Fin 72)
    (he : Function.Surjective e) (hm : xs.toFinset.image (relWord e) = ys.toFinset)
    (hy : ¬ Viable r ys) : ¬ Viable r xs := by
  rintro ⟨k, hk, ht⟩
  have h := ht.relabel e he
  rw [hm] at h
  exact hy ⟨k, hk, h⟩

theorem relWord_by_bits {e : Fin 72 → Fin 72} {a b : Word}
    (h : ∀ i : Fin 72, a.1.getLsbD (e i) = b.1.getLsbD i ∧
      a.2.getLsbD (e i) = b.2.getLsbD i) : relWord e a = b := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact (relBits_at e a.1 ⟨i, hi⟩).trans (h ⟨i, hi⟩).1
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact (relBits_at e a.2 ⟨i, hi⟩).trans (h ⟨i, hi⟩).2

theorem relWord_list {e : Fin 72 → Fin 72} {xs zs ys : List Word}
    (hm : xs.map (relWord e) = zs) (hp : zs.toFinset = ys.toFinset) :
    xs.toFinset.image (relWord e) = ys.toFinset := by
  rw [← hp, ← hm]
  ext w
  simp

end PEqualNP.Outside.Meta617

/- Explicit live-wire states and the tables of their viable children -/

namespace PEqualNP.Outside.Meta617
def mw0q41041041041041041 : Word := (0,74958198140788019265)
def mw0q82082082082082082 : Word := (0,149916396281576038530)
def mw0q104104104104104104 : Word := (0,299832792563152077060)
def mw0q208208208208208208 : Word := (0,599665585126304154120)
def mw0q249249249249249249 : Word := (0,674623783267092173385)
def mw0q30c30c30c30c30c30c : Word := (0,899498377689456231180)
def mw0q410410410410410410 : Word := (0,1199331170252608308240)
def mw0q820820820820820820 : Word := (0,2398662340505216616480)
def mw0qc30c30c30c30c30c30 : Word := (0,3597993510757824924720)
def mw3fq0 : Word := (63,0)
def mw3fq104104104104104104 : Word := (63,299832792563152077060)
def mw3fq208208208208208208 : Word := (63,599665585126304154120)
def mwfc0q0 : Word := (4032,0)
def mwfc0q820820820820820820 : Word := (4032,2398662340505216616480)
def mwfffq0 : Word := (4095,0)
def mw3f000q0 : Word := (258048,0)
def mw3f000q208208208208208208 : Word := (258048,599665585126304154120)
def mw3f000q820820820820820820 : Word := (258048,2398662340505216616480)
def mw3ffffq0 : Word := (262143,0)
def mw3ffffq618618618618618618 : Word := (262143,1798996755378912462360)
def mw3ffffq659659659659659659 : Word := (262143,1873954953519700481625)
def mw3ffffqe38e38e38e38e38e38 : Word := (262143,4197659095884129078840)
def mwfc0000q0 : Word := (16515072,0)
def mwfc0000q208208208208208208 : Word := (16515072,599665585126304154120)
def mwfc0000q820820820820820820 : Word := (16515072,2398662340505216616480)
def mwffffffq618618618618618618 : Word := (16777215,1798996755378912462360)
def mw3f000000q0 : Word := (1056964608,0)
def mw3f000000q82082082082082082 : Word := (1056964608,149916396281576038530)
def mw3f000000q208208208208208208 : Word := (1056964608,599665585126304154120)
def mw3ffc003fq924924924924924924 : Word := (1073479743,2698495133068368693540)
def mw3ffc003fq965965965965965965 : Word := (1073479743,2773453331209156712805)
def mw3ffc003fqb2cb2cb2cb2cb2cb2c : Word := (1073479743,3298160718194672847660)
def mw3ffc0fffq924924924924924924 : Word := (1073483775,2698495133068368693540)
def mw3fffffffqf3cf3cf3cf3cf3cf3c : Word := (1073741823,4497491888447281155900)
def mwfc0000000q0 : Word := (67645734912,0)
def mwfc0000000q820820820820820820 : Word := (67645734912,2398662340505216616480)
def mwfc0fc0000q0 : Word := (67662249984,0)
def mw3f000000000q0 : Word := (4329327034368,0)
def mw3f000000000q104104104104104104 : Word := (4329327034368,299832792563152077060)
def mw3f03ffc003fq924924924924924924 : Word := (4330400514111,2698495133068368693540)
def mw3ffc0000fc0q8a28a28a28a28a28a2 : Word := (4396972773312,2548578736786792655010)
def mw3ffc0000fc0q8e38e38e38e38e38e3 : Word := (4396972773312,2623536934927580674275)
def mw3ffc0000fc0qaaaaaaaaaaaaaaaaaa : Word := (4396972773312,3148244321913096809130)
def mw3ffc0000fffq8a28a28a28a28a28a2 : Word := (4396972773375,2548578736786792655010)
def mw3ffc003ffffqebaebaebaebaebaeba : Word := (4396973031423,4347575492165705117370)
def mw3fffffc0fffq9a69a69a69a69a69a6 : Word := (4398046253055,2848411529349944732070)
def mw3ffffffffffqfbefbefbefbefbefbe : Word := (4398046511103,4647408284728857194430)
def mwfc0000000000q0 : Word := (277076930199552,0)
def mwfc0000000000q820820820820820820 : Word := (277076930199552,2398662340505216616480)
def mwfc0fc0fc0000q249249249249249249 : Word := (277144592449536,674623783267092173385)
def mwfc0fc0fc003fq249249249249249249 : Word := (277144592449599,674623783267092173385)
def mwfc0fc0fc0fffq249249249249249249 : Word := (277144592453631,674623783267092173385)
def mwfc0fc0fff000q249249249249249249 : Word := (277144592707584,674623783267092173385)
def mwfc0fc0ffffffq659659659659659659 : Word := (277144592711679,1873954953519700481625)
def mwfc0ffffc003fqb6db6db6db6db6db6d : Word := (277145649414207,3373118916335460866925)
def mwfc0fffffffffqf7df7df7df7df7df7d : Word := (277145649676287,4572450086588069175165)
def mwffffc0fc0fc0qaebaebaebaebaebaeb : Word := (281473919487936,3223202520053884828395)
def mwfffffffc0fffqbefbefbefbefbefbef : Word := (281474976452607,3523035312617036905455)
def mw3f000000000000q0 : Word := (17732923532771328,0)
def mw3f000000000000q208208208208208208 : Word := (17732923532771328,599665585126304154120)
def mwfc0000000000000q0 : Word := (1134907106097364992,0)
def mwfc0000000000000q208208208208208208 : Word := (1134907106097364992,599665585126304154120)
def mwfff00000003f000q861861861861861861 : Word := (1152640029630394368,2473620538646004635745)
def mwfff00000003f000qa69a69a69a69a69a69 : Word := (1152640029630394368,3073286123772308789865)
def mwfff00000003f03fq861861861861861861 : Word := (1152640029630394431,2473620538646004635745)
def mwfff00000003ffffq861861861861861861 : Word := (1152640029630398463,2473620538646004635745)
def mwfff00000003ffffqe79e79e79e79e79e79 : Word := (1152640029630398463,4272617294024917098105)
def mwfff00003ffff03fq965965965965965965 : Word := (1152640030703874111,2773453331209156712805)
def mwfff00003fffffffqf7df7df7df7df7df7d : Word := (1152640030703878143,4572450086588069175165)
def mwfff03ffc003ffc0q8e38e38e38e38e38e3 : Word := (1152644426603167680,2623536934927580674275)
def mwfff03ffffffffffq9e79e79e79e79e79e7 : Word := (1152644427676647423,2923369727490732751335)
def mwffffc0fc0fff000qa69a69a69a69a69a69 : Word := (1152917174222843904,3073286123772308789865)
def mwffffc0fc0ffffffqe79e79e79e79e79e79 : Word := (1152917174222847999,4272617294024917098105)
def mwffffc0ffffff03fqb6db6db6db6db6db6d : Word := (1152917175279808575,3373118916335460866925)
def mwfffffffc0ffffc0qaebaebaebaebaebaeb : Word := (1152921503549882304,3223202520053884828395)
def mw3f000000000000000q0 : Word := (72634054790231359488,0)
def mw3f03f00003f000000q28a28a28a28a28a28a : Word := (72651787714821095424,749581981407880192650)
def mw3f03f00003f000000q2cb2cb2cb2cb2cb2cb : Word := (72651787714821095424,824540179548668211915)
def mw3f03f00003f00003fq28a28a28a28a28a28a : Word := (72651787714821095487,749581981407880192650)
def mw3f03f00003f000fffq28a28a28a28a28a28a : Word := (72651787714821099519,749581981407880192650)
def mw3f03f00003f03f000q28a28a28a28a28a28a : Word := (72651787714821353472,749581981407880192650)
def mw3f03f00003f03ffffq69a69a69a69a69a69a : Word := (72651787714821357567,1948913151660488500890)
def mw3f03f00003ffc003fqbaebaebaebaebaebae : Word := (72651787714837610559,3448077114476248886190)
def mw3f03f00003fffffffqfbefbefbefbefbefbe : Word := (72651787714837872639,4647408284728857194430)
def mw3f03f03ffff000fc0qaaaaaaaaaaaaaaaaaa : Word := (72651792111793868736,3148244321913096809130)
def mw3f03f03fffffc0fffqbaebaebaebaebaebae : Word := (72651792111810383871,3448077114476248886190)
def mw3f03ffc0ffffc0000q2cb2cb2cb2cb2cb2cb : Word := (72652064859413544960,824540179548668211915)
def mw3ffff00003f03f000qaebaebaebaebaebaeb : Word := (73786694820918718464,3223202520053884828395)
def mw3fffffc0ffffff000qaebaebaebaebaebaeb : Word := (73786971965511168000,3223202520053884828395)
def mwfc0000000000000000q0 : Word := (4648579506574807007232,0)
def mwfc0fc003f000000000q30c30c30c30c30c30c : Word := (4649714418010231406592,899498377689456231180)
def mwfc0fc003f000000000q34d34d34d34d34d34d : Word := (4649714418010231406592,974456575830244250445)
def mwfc0fc003f00000003fq30c30c30c30c30c30c : Word := (4649714418010231406655,899498377689456231180)
def mwfc0fc003f000000fc0q30c30c30c30c30c30c : Word := (4649714418010231410624,899498377689456231180)
def mwfc0fc003f000000fffq30c30c30c30c30c30c : Word := (4649714418010231410687,899498377689456231180)
def mwfc0fc003f00003f000q30c30c30c30c30c30c : Word := (4649714418010231664640,899498377689456231180)
def mwfc0fc003f00003ffffq71c71c71c71c71c71c : Word := (4649714418010231668735,2098829547942064539420)
def mwfc0fc003f03ffc003fqb2cb2cb2cb2cb2cb2c : Word := (4649714418011304886335,3298160718194672847660)
def mwfc0fc003f03fffffffqf3cf3cf3cf3cf3cf3c : Word := (4649714418011305148415,4497491888447281155900)
def mwfc0fc003ffc0000000q30c30c30c30c30c30c : Word := (4649714418077877141504,899498377689456231180)
def mwfc0fc003ffc0000fc0qbaebaebaebaebaebae : Word := (4649714418077877145536,3448077114476248886190)
def mwfc0fc003fffffc0fffqbaebaebaebaebaebae : Word := (4649714418078950625279,3448077114476248886190)
def mwfc0fc0fff000000000q30c30c30c30c30c30c : Word := (4649714695087161606144,899498377689456231180)
def mwfc0fc0ffffc0fc0000q34d34d34d34d34d34d : Word := (4649714695154823856128,974456575830244250445)
def mwfc0fff03f00003f000qb6db6db6db6db6db6d : Word := (4649732150933764435968,3373118916335460866925)
def mwfc0fffffffc0fff000qb6db6db6db6db6db6d : Word := (4649732428078356885504,3373118916335460866925)
def mwfff000fc0000000000qc30c30c30c30c30c30 : Word := (4721213838441968566272,3597993510757824924720)
def mwfff000fc0000000000qc71c71c71c71c71c71 : Word := (4721213838441968566272,3672951708898612943985)
def mwfff000fc0000000000qe38e38e38e38e38e38 : Word := (4721213838441968566272,4197659095884129078840)
def mwfff000fc000000003fqc30c30c30c30c30c30 : Word := (4721213838441968566335,3597993510757824924720)
def mwfff000fc0000000fc0qc30c30c30c30c30c30 : Word := (4721213838441968570304,3597993510757824924720)
def mwfff000fc0000000fffqc30c30c30c30c30c30 : Word := (4721213838441968570367,3597993510757824924720)
def mwfff000fc000003ffffqe38e38e38e38e38e38 : Word := (4721213838441968828415,4197659095884129078840)
def mwfff000fc0000fc0000qc30c30c30c30c30c30 : Word := (4721213838441985081344,3597993510757824924720)
def mwfff000fc0000fc003fqc30c30c30c30c30c30 : Word := (4721213838441985081407,3597993510757824924720)
def mwfff000fc003ffc0000qc30c30c30c30c30c30 : Word := (4721213838443042045952,3597993510757824924720)
def mwfff000fc003ffc003fqd34d34d34d34d34d34 : Word := (4721213838443042046015,3897826303320977001780)
def mwfff000fc003fffffffqf3cf3cf3cf3cf3cf3c : Word := (4721213838443042308095,4497491888447281155900)
def mwfff000fc0fc0000000qc30c30c30c30c30c30 : Word := (4721213838509614301184,3597993510757824924720)
def mwfff000fc0fc0fc0000qc30c30c30c30c30c30 : Word := (4721213838509630816256,3597993510757824924720)
def mwfff000fc0fc0fc0000qe79e79e79e79e79e79 : Word := (4721213838509630816256,4272617294024917098105)
def mwfff000ffffc0000fc0qcb2cb2cb2cb2cb2cb2 : Word := (4721213842838941339584,3747909907039400963250)
def mwfff000fffffffc0fffqdb6db6db6db6db6db6 : Word := (4721213842840014819327,4047742699602553040310)
def mwfff03ffc003f000000qebaebaebaebaebaeba : Word := (4721231571366558302208,4347575492165705117370)
def mwffffc003f000000000q30c30c30c30c30c30c : Word := (4722348472800462766080,899498377689456231180)
def mwffffc0fff000000000qf3cf3cf3cf3cf3cf3c : Word := (4722348749877392965632,4497491888447281155900)
def mwffffff03f03f000000q38e38e38e38e38e38e : Word := (4722366205725052502016,1049414773971032269710)
def mwfffffffc000003f000qc71c71c71c71c71c71 : Word := (4722366478471598960640,3672951708898612943985)
def mwfffffffc0fc0fff000qe79e79e79e79e79e79 : Word := (4722366478539261210624,4272617294024917098105)
def node0 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f03ffffq69a69a69a69a69a69a,mwfff000fc0000000000qc30c30c30c30c30c30,mwffffc003f000000000q30c30c30c30c30c30c]
def tab0 : List (List Word) := []
def node1 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc0fff000000000q30c30c30c30c30c30c,mwfffffffc000003f000qc71c71c71c71c71c71]
def tab1 : List (List Word) := []
def node2 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000fc0000qc30c30c30c30c30c30]
def child2q0 : List Word := [mwfff00003ffff03fq965965965965965965,mw3ffffq618618618618618618,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000fc0000qc30c30c30c30c30c30]
def child2q1 : List Word := [mwfc0fc0ffffc0fc0000q34d34d34d34d34d34d,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000fc0000qc30c30c30c30c30c30]
def tab2 : List (List Word) := [child2q0,child2q1]
def node3 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc003fq249249249249249249,mwfff00000003f03fq861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab3 : List (List Word) := []
def node4 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f03f000q28a28a28a28a28a28a,mwfc0fc003f00003f000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab4 : List (List Word) := []
def node5 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003ffc0000000q30c30c30c30c30c30c,mwfff000fc0fc0000000qc30c30c30c30c30c30]
def tab5 : List (List Word) := []
def node6 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f00003fq28a28a28a28a28a28a,mwfc0fc003f00000003fq30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab6 : List (List Word) := []
def node7 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000fc0q30c30c30c30c30c30c,mwfff000fc0000000fc0qc30c30c30c30c30c30]
def tab7 : List (List Word) := []
def node8 : List Word := [mw3fq0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f00003fq28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child8q0 : List Word := [mw3ffc0000fffq8a28a28a28a28a28a2,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f00003fq28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child8q1 : List Word := [mwfc0fc0fc003fq249249249249249249,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfff00000003f000q861861861861861861,mw3f03f00003f00003fq28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child8q2 : List Word := [mwfff00000003f03fq861861861861861861,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mw3f03f00003f00003fq28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child8q3 : List Word := [mwfc0fc003f00000003fq30c30c30c30c30c30c,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f00003fq28a28a28a28a28a28a,mwfff000fc0000000000qc30c30c30c30c30c30]
def child8q4 : List Word := [mwfff000fc000000003fqc30c30c30c30c30c30,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f00003fq28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c]
def tab8 : List (List Word) := [child8q0,child8q1,child8q2,child8q3,child8q4]
def node9 : List Word := [mw3ffffq618618618618618618,mwffffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab9 : List (List Word) := []
def node10 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fff000q249249249249249249,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30,mwfffffffc000003f000qc71c71c71c71c71c71]
def tab10 : List (List Word) := []
def node11 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc000000003fqc30c30c30c30c30c30]
def child11q0 : List Word := [mwfc0fc003f00003ffffq71c71c71c71c71c71c,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc000000003fqc30c30c30c30c30c30]
def tab11 : List (List Word) := [child11q0]
def node12 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f00000003fq30c30c30c30c30c30c,mwfff000fc000000003fqc30c30c30c30c30c30]
def tab12 : List (List Word) := []
def node13 : List Word := [mw3fq0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc000000003fqc30c30c30c30c30c30]
def child13q0 : List Word := [mw3ffc0000fffq8a28a28a28a28a28a2,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc000000003fqc30c30c30c30c30c30]
def child13q1 : List Word := [mwfc0fc0fc003fq249249249249249249,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc000000003fqc30c30c30c30c30c30]
def child13q2 : List Word := [mwfff00000003f03fq861861861861861861,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc000000003fqc30c30c30c30c30c30]
def child13q3 : List Word := [mw3f03f00003f00003fq28a28a28a28a28a28a,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc000000003fqc30c30c30c30c30c30]
def child13q4 : List Word := [mwfc0fc003f00000003fq30c30c30c30c30c30c,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfff000fc000000003fqc30c30c30c30c30c30]
def tab13 : List (List Word) := [child13q0,child13q1,child13q2,child13q3,child13q4]
def node14 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3f03ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab14 : List (List Word) := []
def node15 : List Word := [mw3fq0,mw3ffffq618618618618618618,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30,mwfff000fc003ffc003fqd34d34d34d34d34d34]
def child15q0 : List Word := [mw3ffc0000fffq8a28a28a28a28a28a2,mw3ffffq618618618618618618,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30,mwfff000fc003ffc003fqd34d34d34d34d34d34]
def child15q1 : List Word := [mwfc0fc0fc003fq249249249249249249,mw3ffffq618618618618618618,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30,mwfff000fc003ffc003fqd34d34d34d34d34d34]
def child15q2 : List Word := [mwfff00000003f03fq861861861861861861,mw3ffffq618618618618618618,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30,mwfff000fc003ffc003fqd34d34d34d34d34d34]
def child15q3 : List Word := [mw3f03f00003f00003fq28a28a28a28a28a28a,mw3ffffq618618618618618618,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30,mwfff000fc003ffc003fqd34d34d34d34d34d34]
def child15q4 : List Word := [mwfc0fc003f00000003fq30c30c30c30c30c30c,mw3ffffq618618618618618618,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfff000fc0000000000qc30c30c30c30c30c30,mwfff000fc003ffc003fqd34d34d34d34d34d34]
def tab15 : List (List Word) := [child15q0,child15q1,child15q2,child15q3,child15q4]
def node16 : List Word := [mw3fq0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child16q0 : List Word := [mw3ffc0000fffq8a28a28a28a28a28a2,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child16q1 : List Word := [mw3ffc0000fffq8a28a28a28a28a28a2,mw3fq0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child16q2 : List Word := [mw3ffc0000fffq8a28a28a28a28a28a2,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child16q3 : List Word := [mwfc0fc0fc003fq249249249249249249,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child16q4 : List Word := [mwfc0fc0fc003fq249249249249249249,mw3fq0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child16q5 : List Word := [mwfc0fc0fc003fq249249249249249249,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child16q6 : List Word := [mwfff00000003f03fq861861861861861861,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child16q7 : List Word := [mwfff00000003f03fq861861861861861861,mw3fq0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child16q8 : List Word := [mwfff00000003f03fq861861861861861861,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child16q9 : List Word := [mw3f03f00003f00003fq28a28a28a28a28a28a,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child16q10 : List Word := [mw3f03f00003f00003fq28a28a28a28a28a28a,mw3fq0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child16q11 : List Word := [mw3f03f00003f00003fq28a28a28a28a28a28a,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child16q12 : List Word := [mwfc0fc003f00000003fq30c30c30c30c30c30c,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfff000fc0000000000qc30c30c30c30c30c30]
def child16q13 : List Word := [mwfc0fc003f00000003fq30c30c30c30c30c30c,mw3fq0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfff000fc0000000000qc30c30c30c30c30c30]
def child16q14 : List Word := [mwfc0fc003f00000003fq30c30c30c30c30c30c,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child16q15 : List Word := [mwfff000fc000000003fqc30c30c30c30c30c30,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c]
def child16q16 : List Word := [mwfff000fc000000003fqc30c30c30c30c30c30,mw3fq0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c]
def child16q17 : List Word := [mwfff000fc000000003fqc30c30c30c30c30c30,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child16q18 : List Word := [mwfc0fc003f00003ffffq71c71c71c71c71c71c,mw3fq0,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child16q19 : List Word := [mwfff000fc003ffc003fqd34d34d34d34d34d34,mw3fq0,mw3ffffq618618618618618618,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab16 : List (List Word) := [child16q0,child16q1,child16q2,child16q3,child16q4,child16q5,child16q6,child16q7,child16q8,child16q9,child16q10,child16q11,child16q12,child16q13,child16q14,child16q15,child16q16,child16q17,child16q18,child16q19]
def node17 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000fc0000qc30c30c30c30c30c30]
def tab17 : List (List Word) := []
def node18 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc003ffc003fqd34d34d34d34d34d34,mwfff000fc0fc0fc0000qe79e79e79e79e79e79]
def child18q0 : List Word := [mwfff000fc0000fc0000qc30c30c30c30c30c30,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c]
def tab18 : List (List Word) := [child18q0]
def node19 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc000000003fqc30c30c30c30c30c30]
def tab19 : List (List Word) := []
def node20 : List Word := [mw3fq208208208208208208,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child20q0 : List Word := [mwfc0fc0fc003fq249249249249249249,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child20q1 : List Word := [mw3f03f00003f00003fq28a28a28a28a28a28a,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child20q2 : List Word := [mwfc0fc003f00000003fq30c30c30c30c30c30c,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab20 : List (List Word) := [child20q0,child20q1,child20q2]
def node21 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mw3ffffffffffqfbefbefbefbefbefbe,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab21 : List (List Word) := []
def node22 : List Word := [mw0q249249249249249249,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab22 : List (List Word) := []
def node23 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mwffffc0fc0ffffffqe79e79e79e79e79e79,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab23 : List (List Word) := []
def node24 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3fffffffqf3cf3cf3cf3cf3cf3c,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child24q0 : List Word := [mwfc0fc0ffffffq659659659659659659,mw3ffc003fq924924924924924924,mw3fffffffqf3cf3cf3cf3cf3cf3c,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child24q1 : List Word := [mw3f03f00003f03ffffq69a69a69a69a69a69a,mw3ffc003fq924924924924924924,mw3fffffffqf3cf3cf3cf3cf3cf3c,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child24q2 : List Word := [mw3fffffc0fffq9a69a69a69a69a69a6,mw3ffffq618618618618618618,mw3fffffffqf3cf3cf3cf3cf3cf3c,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child24q3 : List Word := [mwfff00003ffff03fq965965965965965965,mw3ffffq618618618618618618,mw3fffffffqf3cf3cf3cf3cf3cf3c,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child24q4 : List Word := [mwfc0q820820820820820820,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child24q5 : List Word := [mw3ffffffffffqfbefbefbefbefbefbe,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child24q6 : List Word := [mwfc0000q208208208208208208,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child24q7 : List Word := [mwfc0fffffffffqf7df7df7df7df7df7d,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child24q8 : List Word := [mw3f000q820820820820820820,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child24q9 : List Word := [mwfff00003fffffffqf7df7df7df7df7df7d,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child24q10 : List Word := [mw3f000000q208208208208208208,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child24q11 : List Word := [mw3f03f00003fffffffqfbefbefbefbefbefbe,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child24q12 : List Word := [mw0q30c30c30c30c30c30c,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child24q13 : List Word := [mwfc0fc003f03fffffffqf3cf3cf3cf3cf3cf3c,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child24q14 : List Word := [mw0qc30c30c30c30c30c30,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child24q15 : List Word := [mwfff000fc003fffffffqf3cf3cf3cf3cf3cf3c,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab24 : List (List Word) := [child24q0,child24q1,child24q2,child24q3,child24q4,child24q5,child24q6,child24q7,child24q8,child24q9,child24q10,child24q11,child24q12,child24q13,child24q14,child24q15]
def node25 : List Word := [mw3ffffq618618618618618618,mw3ffffqe38e38e38e38e38e38,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab25 : List (List Word) := []
def node26 : List Word := [mw0q208208208208208208,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child26q0 : List Word := [mw3ffc003fqb2cb2cb2cb2cb2cb2c,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child26q1 : List Word := [mw3ffc0000fc0qaaaaaaaaaaaaaaaaaa,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child26q2 : List Word := [mwfff00000003f000qa69a69a69a69a69a69,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child26q3 : List Word := [mwfff000fc0000000000qe38e38e38e38e38e38,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab26 : List (List Word) := [child26q0,child26q1,child26q2,child26q3]
def node27 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc003ffc0000qc30c30c30c30c30c30]
def tab27 : List (List Word) := []
def node28 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0fc0fc0000qc30c30c30c30c30c30]
def tab28 : List (List Word) := []
def node29 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000fc003fqc30c30c30c30c30c30]
def tab29 : List (List Word) := []
def node30 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000fffqc30c30c30c30c30c30]
def tab30 : List (List Word) := []
def node31 : List Word := [mwfffq0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child31q0 : List Word := [mw3ffc0fffq924924924924924924,mw3ffffq618618618618618618,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child31q1 : List Word := [mw3ffc0000fffq8a28a28a28a28a28a2,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child31q2 : List Word := [mwfc0fc0fc0fffq249249249249249249,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child31q3 : List Word := [mwfff00000003ffffq861861861861861861,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child31q4 : List Word := [mw3f03f00003f000fffq28a28a28a28a28a28a,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child31q5 : List Word := [mwfc0fc003f000000fffq30c30c30c30c30c30c,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfff000fc0000000000qc30c30c30c30c30c30]
def child31q6 : List Word := [mwfff000fc0000000fffqc30c30c30c30c30c30,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c]
def tab31 : List (List Word) := [child31q0,child31q1,child31q2,child31q3,child31q4,child31q5,child31q6]
def node32 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfff00000003f000q861861861861861861,mw3f03ffc0ffffc0000q2cb2cb2cb2cb2cb2cb,mwfc0fc0ffffc0fc0000q34d34d34d34d34d34d,mwfff000fc0000000000qc30c30c30c30c30c30,mwffffff03f03f000000q38e38e38e38e38e38e]
def tab32 : List (List Word) := []
def node33 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab33 : List (List Word) := []
def node34 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc003ffc003fqd34d34d34d34d34d34,mwfff000ffffc0000fc0qcb2cb2cb2cb2cb2cb2]
def child34q0 : List Word := [mw3fffffc0fffq9a69a69a69a69a69a6,mw3ffffq618618618618618618,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc003ffc003fqd34d34d34d34d34d34,mwfff000ffffc0000fc0qcb2cb2cb2cb2cb2cb2]
def child34q1 : List Word := [mwfff000fc0000000000qc30c30c30c30c30c30,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c]
def tab34 : List (List Word) := [child34q0,child34q1]
def node35 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc000003ffffqe38e38e38e38e38e38,mwfff000fc003ffc003fqd34d34d34d34d34d34]
def child35q0 : List Word := [mwfff000fc000000003fqc30c30c30c30c30c30,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c]
def tab35 : List (List Word) := [child35q0]
def node36 : List Word := [mw0q208208208208208208,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab36 : List (List Word) := []
def node37 : List Word := [mw3ffffq0,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab37 : List (List Word) := []
def node38 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mwfff03ffffffffffq9e79e79e79e79e79e7,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child38q0 : List Word := [mw3ffffq0,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab38 : List (List Word) := [child38q0]
def node39 : List Word := [mw3fq104104104104104104,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child39q0 : List Word := [mwfc0fc003f00000003fq30c30c30c30c30c30c,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab39 : List (List Word) := [child39q0]
def node40 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mw3fffffc0fffq9a69a69a69a69a69a6,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q0 : List Word := [mw3fffffffqf3cf3cf3cf3cf3cf3c,mw3ffffq618618618618618618,mw3ffc0000fc0q8a28a28a28a28a28a2,mw3fffffc0fffq9a69a69a69a69a69a6,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q1 : List Word := [mw3ffc003ffffqebaebaebaebaebaeba,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3fffffc0fffq9a69a69a69a69a69a6,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q2 : List Word := [mwfffq0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q3 : List Word := [mw3ffffffffffqfbefbefbefbefbefbe,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q4 : List Word := [mwfc0ffffc003fqb6db6db6db6db6db6d,mw3ffffq618618618618618618,mw3ffc0000fc0q8a28a28a28a28a28a2,mw3fffffc0fffq9a69a69a69a69a69a6,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q5 : List Word := [mwfff00003ffff03fq965965965965965965,mw3ffffq618618618618618618,mw3ffc0000fc0q8a28a28a28a28a28a2,mw3fffffc0fffq9a69a69a69a69a69a6,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q6 : List Word := [mw3f000000q0,mw3ffffq618618618618618618,mw3ffc0000fc0q8a28a28a28a28a28a2,mw3fffffc0fffq9a69a69a69a69a69a6,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q7 : List Word := [mwfc0fc003f03ffc003fqb2cb2cb2cb2cb2cb2c,mw3ffffq618618618618618618,mw3ffc0000fc0q8a28a28a28a28a28a2,mw3fffffc0fffq9a69a69a69a69a69a6,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q8 : List Word := [mwfff000fc003ffc003fqd34d34d34d34d34d34,mw3ffffq618618618618618618,mw3ffc0000fc0q8a28a28a28a28a28a2,mw3fffffc0fffq9a69a69a69a69a69a6,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q9 : List Word := [mwffffc0fc0fc0qaebaebaebaebaebaeb,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3fffffc0fffq9a69a69a69a69a69a6,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q10 : List Word := [mwfff03ffc003ffc0q8e38e38e38e38e38e3,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3fffffc0fffq9a69a69a69a69a69a6,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q11 : List Word := [mw3f03f03ffff000fc0qaaaaaaaaaaaaaaaaaa,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3fffffc0fffq9a69a69a69a69a69a6,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q12 : List Word := [mw3f000000000q0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3fffffc0fffq9a69a69a69a69a69a6,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q13 : List Word := [mwfff000ffffc0000fc0qcb2cb2cb2cb2cb2cb2,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3fffffc0fffq9a69a69a69a69a69a6,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q14 : List Word := [mwfc0fc0000q0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q15 : List Word := [mwfffffffc0fffqbefbefbefbefbefbef,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q16 : List Word := [mw0q820820820820820820,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q17 : List Word := [mwfff03ffffffffffq9e79e79e79e79e79e7,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q18 : List Word := [mw3f000000q82082082082082082,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q19 : List Word := [mw3f03f03fffffc0fffqbaebaebaebaebaebae,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q20 : List Word := [mw3f000000000q104104104104104104,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q21 : List Word := [mwfc0fc003fffffc0fffqbaebaebaebaebaebae,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child40q22 : List Word := [mwfff000fffffffc0fffqdb6db6db6db6db6db6,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab40 : List (List Word) := [child40q0,child40q1,child40q2,child40q3,child40q4,child40q5,child40q6,child40q7,child40q8,child40q9,child40q10,child40q11,child40q12,child40q13,child40q14,child40q15,child40q16,child40q17,child40q18,child40q19,child40q20,child40q21,child40q22]
def node41 : List Word := [mw3ffffq618618618618618618,mw3ffffq659659659659659659,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab41 : List (List Word) := []
def node42 : List Word := [mw0q41041041041041041,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child42q0 : List Word := [mw3ffffq659659659659659659,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child42q1 : List Word := [mw3ffc003fq965965965965965965,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child42q2 : List Word := [mw3ffc0000fc0q8e38e38e38e38e38e3,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child42q3 : List Word := [mw3f03f00003f000000q2cb2cb2cb2cb2cb2cb,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child42q4 : List Word := [mwfc0fc003f000000000q34d34d34d34d34d34d,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child42q5 : List Word := [mwfff000fc0000000000qc71c71c71c71c71c71,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab42 : List (List Word) := [child42q0,child42q1,child42q2,child42q3,child42q4,child42q5]
def node43 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mwffffc0fc0fff000qa69a69a69a69a69a69,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child43q0 : List Word := [mwfc0fc0ffffffq659659659659659659,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfff00000003f000q861861861861861861,mwffffc0fc0fff000qa69a69a69a69a69a69,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child43q1 : List Word := [mw3f000q208208208208208208,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child43q2 : List Word := [mwffffc0fc0ffffffqe79e79e79e79e79e79,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child43q3 : List Word := [mwfff00003ffff03fq965965965965965965,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwffffc0fc0fff000qa69a69a69a69a69a69,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child43q4 : List Word := [mwfc0000q820820820820820820,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child43q5 : List Word := [mwffffc0ffffff03fqb6db6db6db6db6db6d,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child43q6 : List Word := [mwfff03ffc003ffc0q8e38e38e38e38e38e3,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwffffc0fc0fff000qa69a69a69a69a69a69,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child43q7 : List Word := [mwfc0000000q820820820820820820,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child43q8 : List Word := [mwfffffffc0ffffc0qaebaebaebaebaebaeb,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child43q9 : List Word := [mw3f03ffc0ffffc0000q2cb2cb2cb2cb2cb2cb,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfff00000003f000q861861861861861861,mwffffc0fc0fff000qa69a69a69a69a69a69,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child43q10 : List Word := [mwfc0fc0ffffc0fc0000q34d34d34d34d34d34d,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfff00000003f000q861861861861861861,mwffffc0fc0fff000qa69a69a69a69a69a69,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child43q11 : List Word := [mwfffffffc000003f000qc71c71c71c71c71c71,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwffffc0fc0fff000qa69a69a69a69a69a69,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child43q12 : List Word := [mw3f000000000000q208208208208208208,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child43q13 : List Word := [mw3fffffc0ffffff000qaebaebaebaebaebaeb,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child43q14 : List Word := [mwfc0000000000000q208208208208208208,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child43q15 : List Word := [mwfc0fffffffc0fff000qb6db6db6db6db6db6d,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child43q16 : List Word := [mwfc0000000000q820820820820820820,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child43q17 : List Word := [mwfffffffc0fc0fff000qe79e79e79e79e79e79,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab43 : List (List Word) := [child43q0,child43q1,child43q2,child43q3,child43q4,child43q5,child43q6,child43q7,child43q8,child43q9,child43q10,child43q11,child43q12,child43q13,child43q14,child43q15,child43q16,child43q17]
def node44 : List Word := [mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q0 : List Word := [mw3fq0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q1 : List Word := [mw3fffffffqf3cf3cf3cf3cf3cf3c,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q2 : List Word := [mwfc0q0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q3 : List Word := [mw3ffc003ffffqebaebaebaebaebaeba,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q4 : List Word := [mw0q208208208208208208,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q5 : List Word := [mwfc0fc0ffffffq659659659659659659,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q6 : List Word := [mw3f000q0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q7 : List Word := [mwfff00000003ffffqe79e79e79e79e79e79,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q8 : List Word := [mw3f03f00003f03ffffq69a69a69a69a69a69a,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q9 : List Word := [mwfc0fc003f00003ffffq71c71c71c71c71c71c,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q10 : List Word := [mw0q410410410410410410,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q11 : List Word := [mwfff000fc000003ffffqe38e38e38e38e38e38,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q12 : List Word := [mw0q820820820820820820,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q13 : List Word := [mw3fffffc0fffq9a69a69a69a69a69a6,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q14 : List Word := [mwfc0000q0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q15 : List Word := [mwfc0ffffc003fqb6db6db6db6db6db6d,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q16 : List Word := [mwfff00003ffff03fq965965965965965965,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q17 : List Word := [mw3f000000q0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q18 : List Word := [mw3f03f00003ffc003fqbaebaebaebaebaebae,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q19 : List Word := [mw0q104104104104104104,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q20 : List Word := [mwfc0fc003f03ffc003fqb2cb2cb2cb2cb2cb2c,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q21 : List Word := [mwfff000fc003ffc003fqd34d34d34d34d34d34,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q22 : List Word := [mwfc0000000q0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q23 : List Word := [mwffffc0fc0fc0qaebaebaebaebaebaeb,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q24 : List Word := [mwfff03ffc003ffc0q8e38e38e38e38e38e3,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q25 : List Word := [mw0q82082082082082082,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q26 : List Word := [mw3f03f03ffff000fc0qaaaaaaaaaaaaaaaaaa,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q27 : List Word := [mw3f000000000q0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q28 : List Word := [mwfc0fc003ffc0000fc0qbaebaebaebaebaebae,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q29 : List Word := [mwfff000ffffc0000fc0qcb2cb2cb2cb2cb2cb2,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q30 : List Word := [mw0q41041041041041041,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q31 : List Word := [mwffffc0fc0fff000qa69a69a69a69a69a69,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q32 : List Word := [mw3f03ffc0ffffc0000q2cb2cb2cb2cb2cb2cb,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q33 : List Word := [mwfc0fc0ffffc0fc0000q34d34d34d34d34d34d,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q34 : List Word := [mwfc0000000000q0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q35 : List Word := [mwfff000fc0fc0fc0000qe79e79e79e79e79e79,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q36 : List Word := [mw3f000000000000q0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q37 : List Word := [mw3ffff00003f03f000qaebaebaebaebaebaeb,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q38 : List Word := [mwfc0000000000000q0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q39 : List Word := [mwfc0fff03f00003f000qb6db6db6db6db6db6d,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q40 : List Word := [mwfffffffc000003f000qc71c71c71c71c71c71,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q41 : List Word := [mwffffff03f03f000000q38e38e38e38e38e38e,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q42 : List Word := [mw3f000000000000000q0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q43 : List Word := [mwfff03ffc003f000000qebaebaebaebaebaeba,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q44 : List Word := [mwfc0000000000000000q0,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def child44q45 : List Word := [mwffffc0fff000000000qf3cf3cf3cf3cf3cf3c,mw3ffffq618618618618618618,mw3ffc003fq924924924924924924,mw3ffc0000fc0q8a28a28a28a28a28a2,mwfc0fc0fc0000q249249249249249249,mwfff00000003f000q861861861861861861,mw3f03f00003f000000q28a28a28a28a28a28a,mwfc0fc003f000000000q30c30c30c30c30c30c,mwfff000fc0000000000qc30c30c30c30c30c30]
def tab44 : List (List Word) := [child44q0,child44q1,child44q2,child44q3,child44q4,child44q5,child44q6,child44q7,child44q8,child44q9,child44q10,child44q11,child44q12,child44q13,child44q14,child44q15,child44q16,child44q17,child44q18,child44q19,child44q20,child44q21,child44q22,child44q23,child44q24,child44q25,child44q26,child44q27,child44q28,child44q29,child44q30,child44q31,child44q32,child44q33,child44q34,child44q35,child44q36,child44q37,child44q38,child44q39,child44q40,child44q41,child44q42,child44q43,child44q44,child44q45]
end PEqualNP.Outside.Meta617

/- The concrete permutations of the 72 example pairs and their inverses -/

namespace PEqualNP.Outside.Meta617
def p0 (i : Fin 72) : Fin 72 := ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71] : List (Fin 72)).getD i 0
private def pi0 (i : Fin 72) : Fin 72 := ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71] : List (Fin 72)).getD i 0
theorem sur0 : Function.Surjective p0 := by
  have h : ∀ i : Fin 72, p0 (pi0 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p1 (i : Fin 72) : Fin 72 := ([1,0,2,3,4,5,13,12,14,15,16,17,7,6,8,9,10,11,25,24,26,27,28,29,19,18,20,21,22,23,49,48,50,51,52,53,55,54,56,57,58,59,61,60,62,63,64,65,31,30,32,33,34,35,37,36,38,39,40,41,43,42,44,45,46,47,67,66,68,69,70,71] : List (Fin 72)).getD i 0
private def pi1 (i : Fin 72) : Fin 72 := ([1,0,2,3,4,5,13,12,14,15,16,17,7,6,8,9,10,11,25,24,26,27,28,29,19,18,20,21,22,23,49,48,50,51,52,53,55,54,56,57,58,59,61,60,62,63,64,65,31,30,32,33,34,35,37,36,38,39,40,41,43,42,44,45,46,47,67,66,68,69,70,71] : List (Fin 72)).getD i 0
theorem sur1 : Function.Surjective p1 := by
  have h : ∀ i : Fin 72, p1 (pi1 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p2 (i : Fin 72) : Fin 72 := ([6,8,7,9,10,11,0,2,1,3,4,5,12,14,13,15,16,17,30,32,31,33,34,35,36,38,37,39,40,41,18,20,19,21,22,23,24,26,25,27,28,29,42,44,43,45,46,47,54,56,55,57,58,59,48,50,49,51,52,53,66,68,67,69,70,71,60,62,61,63,64,65] : List (Fin 72)).getD i 0
private def pi2 (i : Fin 72) : Fin 72 := ([6,8,7,9,10,11,0,2,1,3,4,5,12,14,13,15,16,17,30,32,31,33,34,35,36,38,37,39,40,41,18,20,19,21,22,23,24,26,25,27,28,29,42,44,43,45,46,47,54,56,55,57,58,59,48,50,49,51,52,53,66,68,67,69,70,71,60,62,61,63,64,65] : List (Fin 72)).getD i 0
theorem sur2 : Function.Surjective p2 := by
  have h : ∀ i : Fin 72, p2 (pi2 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p3 (i : Fin 72) : Fin 72 := ([13,14,12,15,16,17,1,2,0,3,4,5,7,8,6,9,10,11,49,50,48,51,52,53,55,56,54,57,58,59,25,26,24,27,28,29,19,20,18,21,22,23,61,62,60,63,64,65,37,38,36,39,40,41,31,32,30,33,34,35,67,68,66,69,70,71,43,44,42,45,46,47] : List (Fin 72)).getD i 0
private def pi3 (i : Fin 72) : Fin 72 := ([8,6,7,9,10,11,14,12,13,15,16,17,2,0,1,3,4,5,38,36,37,39,40,41,32,30,31,33,34,35,56,54,55,57,58,59,50,48,49,51,52,53,68,66,67,69,70,71,20,18,19,21,22,23,26,24,25,27,28,29,44,42,43,45,46,47,62,60,61,63,64,65] : List (Fin 72)).getD i 0
theorem sur3 : Function.Surjective p3 := by
  have h : ∀ i : Fin 72, p3 (pi3 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p4 (i : Fin 72) : Fin 72 := ([8,6,7,9,10,11,14,12,13,15,16,17,2,0,1,3,4,5,38,36,37,39,40,41,32,30,31,33,34,35,56,54,55,57,58,59,50,48,49,51,52,53,68,66,67,69,70,71,20,18,19,21,22,23,26,24,25,27,28,29,44,42,43,45,46,47,62,60,61,63,64,65] : List (Fin 72)).getD i 0
private def pi4 (i : Fin 72) : Fin 72 := ([13,14,12,15,16,17,1,2,0,3,4,5,7,8,6,9,10,11,49,50,48,51,52,53,55,56,54,57,58,59,25,26,24,27,28,29,19,20,18,21,22,23,61,62,60,63,64,65,37,38,36,39,40,41,31,32,30,33,34,35,67,68,66,69,70,71,43,44,42,45,46,47] : List (Fin 72)).getD i 0
theorem sur4 : Function.Surjective p4 := by
  have h : ∀ i : Fin 72, p4 (pi4 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p6 (i : Fin 72) : Fin 72 := ([1,0,4,5,2,3,19,18,22,23,20,21,25,24,28,29,26,27,7,6,10,11,8,9,13,12,16,17,14,15,31,30,34,35,32,33,43,42,46,47,44,45,37,36,40,41,38,39,49,48,52,53,50,51,61,60,64,65,62,63,55,54,58,59,56,57,67,66,70,71,68,69] : List (Fin 72)).getD i 0
private def pi6 (i : Fin 72) : Fin 72 := ([1,0,4,5,2,3,19,18,22,23,20,21,25,24,28,29,26,27,7,6,10,11,8,9,13,12,16,17,14,15,31,30,34,35,32,33,43,42,46,47,44,45,37,36,40,41,38,39,49,48,52,53,50,51,61,60,64,65,62,63,55,54,58,59,56,57,67,66,70,71,68,69] : List (Fin 72)).getD i 0
theorem sur6 : Function.Surjective p6 := by
  have h : ∀ i : Fin 72, p6 (pi6 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p7 (i : Fin 72) : Fin 72 := ([0,1,4,5,2,3,24,25,28,29,26,27,18,19,22,23,20,21,12,13,16,17,14,15,6,7,10,11,8,9,48,49,52,53,50,51,60,61,64,65,62,63,54,55,58,59,56,57,30,31,34,35,32,33,42,43,46,47,44,45,36,37,40,41,38,39,66,67,70,71,68,69] : List (Fin 72)).getD i 0
private def pi7 (i : Fin 72) : Fin 72 := ([0,1,4,5,2,3,24,25,28,29,26,27,18,19,22,23,20,21,12,13,16,17,14,15,6,7,10,11,8,9,48,49,52,53,50,51,60,61,64,65,62,63,54,55,58,59,56,57,30,31,34,35,32,33,42,43,46,47,44,45,36,37,40,41,38,39,66,67,70,71,68,69] : List (Fin 72)).getD i 0
theorem sur7 : Function.Surjective p7 := by
  have h : ∀ i : Fin 72, p7 (pi7 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p8 (i : Fin 72) : Fin 72 := ([8,6,10,11,7,9,32,30,34,35,31,33,38,36,40,41,37,39,2,0,4,5,1,3,14,12,16,17,13,15,20,18,22,23,19,21,44,42,46,47,43,45,26,24,28,29,25,27,56,54,58,59,55,57,68,66,70,71,67,69,50,48,52,53,49,51,62,60,64,65,61,63] : List (Fin 72)).getD i 0
private def pi8 (i : Fin 72) : Fin 72 := ([19,22,18,23,20,21,1,4,0,5,2,3,25,28,24,29,26,27,31,34,30,35,32,33,43,46,42,47,44,45,7,10,6,11,8,9,13,16,12,17,14,15,37,40,36,41,38,39,61,64,60,65,62,63,49,52,48,53,50,51,67,70,66,71,68,69,55,58,54,59,56,57] : List (Fin 72)).getD i 0
theorem sur8 : Function.Surjective p8 := by
  have h : ∀ i : Fin 72, p8 (pi8 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p9 (i : Fin 72) : Fin 72 := ([14,13,16,17,12,15,50,49,52,53,48,51,56,55,58,59,54,57,2,1,4,5,0,3,8,7,10,11,6,9,26,25,28,29,24,27,62,61,64,65,60,63,20,19,22,23,18,21,38,37,40,41,36,39,68,67,70,71,66,69,32,31,34,35,30,33,44,43,46,47,42,45] : List (Fin 72)).getD i 0
private def pi9 (i : Fin 72) : Fin 72 := ([22,19,18,23,20,21,28,25,24,29,26,27,4,1,0,5,2,3,46,43,42,47,44,45,34,31,30,35,32,33,64,61,60,65,62,63,52,49,48,53,50,51,70,67,66,71,68,69,10,7,6,11,8,9,16,13,12,17,14,15,40,37,36,41,38,39,58,55,54,59,56,57] : List (Fin 72)).getD i 0
theorem sur9 : Function.Surjective p9 := by
  have h : ∀ i : Fin 72, p9 (pi9 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p10 (i : Fin 72) : Fin 72 := ([6,8,10,11,7,9,36,38,40,41,37,39,30,32,34,35,31,33,12,14,16,17,13,15,0,2,4,5,1,3,54,56,58,59,55,57,66,68,70,71,67,69,48,50,52,53,49,51,18,20,22,23,19,21,42,44,46,47,43,45,24,26,28,29,25,27,60,62,64,65,61,63] : List (Fin 72)).getD i 0
private def pi10 (i : Fin 72) : Fin 72 := ([24,28,25,29,26,27,0,4,1,5,2,3,18,22,19,23,20,21,48,52,49,53,50,51,60,64,61,65,62,63,12,16,13,17,14,15,6,10,7,11,8,9,54,58,55,59,56,57,42,46,43,47,44,45,30,34,31,35,32,33,66,70,67,71,68,69,36,40,37,41,38,39] : List (Fin 72)).getD i 0
theorem sur10 : Function.Surjective p10 := by
  have h : ∀ i : Fin 72, p10 (pi10 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p11 (i : Fin 72) : Fin 72 := ([13,14,16,17,12,15,55,56,58,59,54,57,49,50,52,53,48,51,7,8,10,11,6,9,1,2,4,5,0,3,37,38,40,41,36,39,67,68,70,71,66,69,31,32,34,35,30,33,25,26,28,29,24,27,61,62,64,65,60,63,19,20,22,23,18,21,43,44,46,47,42,45] : List (Fin 72)).getD i 0
private def pi11 (i : Fin 72) : Fin 72 := ([28,24,25,29,26,27,22,18,19,23,20,21,4,0,1,5,2,3,64,60,61,65,62,63,52,48,49,53,50,51,46,42,43,47,44,45,34,30,31,35,32,33,70,66,67,71,68,69,16,12,13,17,14,15,10,6,7,11,8,9,58,54,55,59,56,57,40,36,37,41,38,39] : List (Fin 72)).getD i 0
theorem sur11 : Function.Surjective p11 := by
  have h : ∀ i : Fin 72, p11 (pi11 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p12 (i : Fin 72) : Fin 72 := ([32,34,30,35,31,33,8,10,6,11,7,9,38,40,36,41,37,39,20,22,18,23,19,21,44,46,42,47,43,45,2,4,0,5,1,3,14,16,12,17,13,15,26,28,24,29,25,27,68,70,66,71,67,69,56,58,54,59,55,57,62,64,60,65,61,63,50,52,48,53,49,51] : List (Fin 72)).getD i 0
private def pi12 (i : Fin 72) : Fin 72 := ([32,34,30,35,31,33,8,10,6,11,7,9,38,40,36,41,37,39,20,22,18,23,19,21,44,46,42,47,43,45,2,4,0,5,1,3,14,16,12,17,13,15,26,28,24,29,25,27,68,70,66,71,67,69,56,58,54,59,55,57,62,64,60,65,61,63,50,52,48,53,49,51] : List (Fin 72)).getD i 0
theorem sur12 : Function.Surjective p12 := by
  have h : ∀ i : Fin 72, p12 (pi12 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p13 (i : Fin 72) : Fin 72 := ([50,52,49,53,48,51,14,16,13,17,12,15,56,58,55,59,54,57,26,28,25,29,24,27,62,64,61,65,60,63,2,4,1,5,0,3,8,10,7,11,6,9,20,22,19,23,18,21,68,70,67,71,66,69,38,40,37,41,36,39,44,46,43,47,42,45,32,34,31,35,30,33] : List (Fin 72)).getD i 0
private def pi13 (i : Fin 72) : Fin 72 := ([34,32,30,35,31,33,40,38,36,41,37,39,10,8,6,11,7,9,46,44,42,47,43,45,22,20,18,23,19,21,70,68,66,71,67,69,58,56,54,59,55,57,64,62,60,65,61,63,4,2,0,5,1,3,16,14,12,17,13,15,28,26,24,29,25,27,52,50,48,53,49,51] : List (Fin 72)).getD i 0
theorem sur13 : Function.Surjective p13 := by
  have h : ∀ i : Fin 72, p13 (pi13 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p14 (i : Fin 72) : Fin 72 := ([19,22,18,23,20,21,1,4,0,5,2,3,25,28,24,29,26,27,31,34,30,35,32,33,43,46,42,47,44,45,7,10,6,11,8,9,13,16,12,17,14,15,37,40,36,41,38,39,61,64,60,65,62,63,49,52,48,53,50,51,67,70,66,71,68,69,55,58,54,59,56,57] : List (Fin 72)).getD i 0
private def pi14 (i : Fin 72) : Fin 72 := ([8,6,10,11,7,9,32,30,34,35,31,33,38,36,40,41,37,39,2,0,4,5,1,3,14,12,16,17,13,15,20,18,22,23,19,21,44,42,46,47,43,45,26,24,28,29,25,27,56,54,58,59,55,57,68,66,70,71,67,69,50,48,52,53,49,51,62,60,64,65,61,63] : List (Fin 72)).getD i 0
theorem sur14 : Function.Surjective p14 := by
  have h : ∀ i : Fin 72, p14 (pi14 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p15 (i : Fin 72) : Fin 72 := ([24,28,25,29,26,27,0,4,1,5,2,3,18,22,19,23,20,21,48,52,49,53,50,51,60,64,61,65,62,63,12,16,13,17,14,15,6,10,7,11,8,9,54,58,55,59,56,57,42,46,43,47,44,45,30,34,31,35,32,33,66,70,67,71,68,69,36,40,37,41,38,39] : List (Fin 72)).getD i 0
private def pi15 (i : Fin 72) : Fin 72 := ([6,8,10,11,7,9,36,38,40,41,37,39,30,32,34,35,31,33,12,14,16,17,13,15,0,2,4,5,1,3,54,56,58,59,55,57,66,68,70,71,67,69,48,50,52,53,49,51,18,20,22,23,19,21,42,44,46,47,43,45,24,26,28,29,25,27,60,62,64,65,61,63] : List (Fin 72)).getD i 0
theorem sur15 : Function.Surjective p15 := by
  have h : ∀ i : Fin 72, p15 (pi15 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p16 (i : Fin 72) : Fin 72 := ([55,58,56,59,54,57,13,16,14,17,12,15,49,52,50,53,48,51,37,40,38,41,36,39,67,70,68,71,66,69,7,10,8,11,6,9,1,4,2,5,0,3,31,34,32,35,30,33,61,64,62,65,60,63,25,28,26,29,24,27,43,46,44,47,42,45,19,22,20,23,18,21] : List (Fin 72)).getD i 0
private def pi16 (i : Fin 72) : Fin 72 := ([40,36,38,41,37,39,34,30,32,35,31,33,10,6,8,11,7,9,70,66,68,71,67,69,58,54,56,59,55,57,46,42,44,47,43,45,22,18,20,23,19,21,64,60,62,65,61,63,16,12,14,17,13,15,4,0,2,5,1,3,52,48,50,53,49,51,28,24,26,29,25,27] : List (Fin 72)).getD i 0
theorem sur16 : Function.Surjective p16 := by
  have h : ∀ i : Fin 72, p16 (pi16 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p17 (i : Fin 72) : Fin 72 := ([36,40,38,41,37,39,6,10,8,11,7,9,30,34,32,35,31,33,54,58,56,59,55,57,66,70,68,71,67,69,12,16,14,17,13,15,0,4,2,5,1,3,48,52,50,53,49,51,42,46,44,47,43,45,18,22,20,23,19,21,60,64,62,65,61,63,24,28,26,29,25,27] : List (Fin 72)).getD i 0
private def pi17 (i : Fin 72) : Fin 72 := ([36,40,38,41,37,39,6,10,8,11,7,9,30,34,32,35,31,33,54,58,56,59,55,57,66,70,68,71,67,69,12,16,14,17,13,15,0,4,2,5,1,3,48,52,50,53,49,51,42,46,44,47,43,45,18,22,20,23,19,21,60,64,62,65,61,63,24,28,26,29,25,27] : List (Fin 72)).getD i 0
theorem sur17 : Function.Surjective p17 := by
  have h : ∀ i : Fin 72, p17 (pi17 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p18 (i : Fin 72) : Fin 72 := ([34,32,31,33,30,35,22,20,19,21,18,23,46,44,43,45,42,47,10,8,7,9,6,11,40,38,37,39,36,41,4,2,1,3,0,5,28,26,25,27,24,29,16,14,13,15,12,17,70,68,67,69,66,71,64,62,61,63,60,65,58,56,55,57,54,59,52,50,49,51,48,53] : List (Fin 72)).getD i 0
private def pi18 (i : Fin 72) : Fin 72 := ([34,32,31,33,30,35,22,20,19,21,18,23,46,44,43,45,42,47,10,8,7,9,6,11,40,38,37,39,36,41,4,2,1,3,0,5,28,26,25,27,24,29,16,14,13,15,12,17,70,68,67,69,66,71,64,62,61,63,60,65,58,56,55,57,54,59,52,50,49,51,48,53] : List (Fin 72)).getD i 0
theorem sur18 : Function.Surjective p18 := by
  have h : ∀ i : Fin 72, p18 (pi18 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p19 (i : Fin 72) : Fin 72 := ([52,50,48,51,49,53,28,26,24,27,25,29,64,62,60,63,61,65,16,14,12,15,13,17,58,56,54,57,55,59,4,2,0,3,1,5,22,20,18,21,19,23,10,8,6,9,7,11,70,68,66,69,67,71,46,44,42,45,43,47,40,38,36,39,37,41,34,32,30,33,31,35] : List (Fin 72)).getD i 0
private def pi19 (i : Fin 72) : Fin 72 := ([32,34,31,33,30,35,44,46,43,45,42,47,20,22,19,21,18,23,38,40,37,39,36,41,8,10,7,9,6,11,68,70,67,69,66,71,62,64,61,63,60,65,56,58,55,57,54,59,2,4,1,3,0,5,26,28,25,27,24,29,14,16,13,15,12,17,50,52,49,51,48,53] : List (Fin 72)).getD i 0
theorem sur19 : Function.Surjective p19 := by
  have h : ∀ i : Fin 72, p19 (pi19 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p20 (i : Fin 72) : Fin 72 := ([22,19,20,21,18,23,34,31,32,33,30,35,46,43,44,45,42,47,4,1,2,3,0,5,28,25,26,27,24,29,10,7,8,9,6,11,40,37,38,39,36,41,16,13,14,15,12,17,64,61,62,63,60,65,70,67,68,69,66,71,52,49,50,51,48,53,58,55,56,57,54,59] : List (Fin 72)).getD i 0
private def pi20 (i : Fin 72) : Fin 72 := ([22,19,20,21,18,23,34,31,32,33,30,35,46,43,44,45,42,47,4,1,2,3,0,5,28,25,26,27,24,29,10,7,8,9,6,11,40,37,38,39,36,41,16,13,14,15,12,17,64,61,62,63,60,65,70,67,68,69,66,71,52,49,50,51,48,53,58,55,56,57,54,59] : List (Fin 72)).getD i 0
theorem sur20 : Function.Surjective p20 := by
  have h : ∀ i : Fin 72, p20 (pi20 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p21 (i : Fin 72) : Fin 72 := ([28,24,26,27,25,29,52,48,50,51,49,53,64,60,62,63,61,65,4,0,2,3,1,5,22,18,20,21,19,23,16,12,14,15,13,17,58,54,56,57,55,59,10,6,8,9,7,11,46,42,44,45,43,47,70,66,68,69,67,71,34,30,32,33,31,35,40,36,38,39,37,41] : List (Fin 72)).getD i 0
private def pi21 (i : Fin 72) : Fin 72 := ([19,22,20,21,18,23,43,46,44,45,42,47,31,34,32,33,30,35,25,28,26,27,24,29,1,4,2,3,0,5,61,64,62,63,60,65,67,70,68,69,66,71,49,52,50,51,48,53,7,10,8,9,6,11,37,40,38,39,36,41,13,16,14,15,12,17,55,58,56,57,54,59] : List (Fin 72)).getD i 0
theorem sur21 : Function.Surjective p21 := by
  have h : ∀ i : Fin 72, p21 (pi21 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p22 (i : Fin 72) : Fin 72 := ([58,55,54,57,56,59,40,37,36,39,38,41,70,67,66,69,68,71,16,13,12,15,14,17,52,49,48,51,50,53,10,7,6,9,8,11,34,31,30,33,32,35,4,1,0,3,2,5,64,61,60,63,62,65,46,43,42,45,44,47,28,25,24,27,26,29,22,19,18,21,20,23] : List (Fin 72)).getD i 0
private def pi22 (i : Fin 72) : Fin 72 := ([44,43,46,45,42,47,32,31,34,33,30,35,20,19,22,21,18,23,68,67,70,69,66,71,62,61,64,63,60,65,38,37,40,39,36,41,8,7,10,9,6,11,56,55,58,57,54,59,26,25,28,27,24,29,2,1,4,3,0,5,50,49,52,51,48,53,14,13,16,15,12,17] : List (Fin 72)).getD i 0
theorem sur22 : Function.Surjective p22 := by
  have h : ∀ i : Fin 72, p22 (pi22 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p23 (i : Fin 72) : Fin 72 := ([40,36,37,39,38,41,58,54,55,57,56,59,70,66,67,69,68,71,10,6,7,9,8,11,34,30,31,33,32,35,16,12,13,15,14,17,52,48,49,51,50,53,4,0,1,3,2,5,46,42,43,45,44,47,64,60,61,63,62,65,22,18,19,21,20,23,28,24,25,27,26,29] : List (Fin 72)).getD i 0
private def pi23 (i : Fin 72) : Fin 72 := ([43,44,46,45,42,47,19,20,22,21,18,23,31,32,34,33,30,35,61,62,64,63,60,65,67,68,70,69,66,71,25,26,28,27,24,29,1,2,4,3,0,5,49,50,52,51,48,53,37,38,40,39,36,41,7,8,10,9,6,11,55,56,58,57,54,59,13,14,16,15,12,17] : List (Fin 72)).getD i 0
theorem sur23 : Function.Surjective p23 := by
  have h : ∀ i : Fin 72, p23 (pi23 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p24 (i : Fin 72) : Fin 72 := ([52,50,49,53,48,51,58,56,55,59,54,57,16,14,13,17,12,15,64,62,61,65,60,63,28,26,25,29,24,27,70,68,67,71,66,69,40,38,37,41,36,39,46,44,43,47,42,45,4,2,1,5,0,3,10,8,7,11,6,9,22,20,19,23,18,21,34,32,31,35,30,33] : List (Fin 72)).getD i 0
private def pi24 (i : Fin 72) : Fin 72 := ([52,50,49,53,48,51,58,56,55,59,54,57,16,14,13,17,12,15,64,62,61,65,60,63,28,26,25,29,24,27,70,68,67,71,66,69,40,38,37,41,36,39,46,44,43,47,42,45,4,2,1,5,0,3,10,8,7,11,6,9,22,20,19,23,18,21,34,32,31,35,30,33] : List (Fin 72)).getD i 0
theorem sur24 : Function.Surjective p24 := by
  have h : ∀ i : Fin 72, p24 (pi24 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p25 (i : Fin 72) : Fin 72 := ([34,32,30,35,31,33,40,38,36,41,37,39,10,8,6,11,7,9,46,44,42,47,43,45,22,20,18,23,19,21,70,68,66,71,67,69,58,56,54,59,55,57,64,62,60,65,61,63,4,2,0,5,1,3,16,14,12,17,13,15,28,26,24,29,25,27,52,50,48,53,49,51] : List (Fin 72)).getD i 0
private def pi25 (i : Fin 72) : Fin 72 := ([50,52,49,53,48,51,14,16,13,17,12,15,56,58,55,59,54,57,26,28,25,29,24,27,62,64,61,65,60,63,2,4,1,5,0,3,8,10,7,11,6,9,20,22,19,23,18,21,68,70,67,71,66,69,38,40,37,41,36,39,44,46,43,47,42,45,32,34,31,35,30,33] : List (Fin 72)).getD i 0
theorem sur25 : Function.Surjective p25 := by
  have h : ∀ i : Fin 72, p25 (pi25 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p28 (i : Fin 72) : Fin 72 := ([22,19,18,23,20,21,28,25,24,29,26,27,4,1,0,5,2,3,46,43,42,47,44,45,34,31,30,35,32,33,64,61,60,65,62,63,52,49,48,53,50,51,70,67,66,71,68,69,10,7,6,11,8,9,16,13,12,17,14,15,40,37,36,41,38,39,58,55,54,59,56,57] : List (Fin 72)).getD i 0
private def pi28 (i : Fin 72) : Fin 72 := ([14,13,16,17,12,15,50,49,52,53,48,51,56,55,58,59,54,57,2,1,4,5,0,3,8,7,10,11,6,9,26,25,28,29,24,27,62,61,64,65,60,63,20,19,22,23,18,21,38,37,40,41,36,39,68,67,70,71,66,69,32,31,34,35,30,33,44,43,46,47,42,45] : List (Fin 72)).getD i 0
theorem sur28 : Function.Surjective p28 := by
  have h : ∀ i : Fin 72, p28 (pi28 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p30 (i : Fin 72) : Fin 72 := ([50,52,48,51,49,53,62,64,60,63,61,65,26,28,24,27,25,29,56,58,54,57,55,59,14,16,12,15,13,17,68,70,66,69,67,71,44,46,42,45,43,47,38,40,36,39,37,41,2,4,0,3,1,5,20,22,18,21,19,23,8,10,6,9,7,11,32,34,30,33,31,35] : List (Fin 72)).getD i 0
private def pi30 (i : Fin 72) : Fin 72 := ([50,52,48,51,49,53,62,64,60,63,61,65,26,28,24,27,25,29,56,58,54,57,55,59,14,16,12,15,13,17,68,70,66,69,67,71,44,46,42,45,43,47,38,40,36,39,37,41,2,4,0,3,1,5,20,22,18,21,19,23,8,10,6,9,7,11,32,34,30,33,31,35] : List (Fin 72)).getD i 0
theorem sur30 : Function.Surjective p30 := by
  have h : ∀ i : Fin 72, p30 (pi30 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p31 (i : Fin 72) : Fin 72 := ([32,34,31,33,30,35,44,46,43,45,42,47,20,22,19,21,18,23,38,40,37,39,36,41,8,10,7,9,6,11,68,70,67,69,66,71,62,64,61,63,60,65,56,58,55,57,54,59,2,4,1,3,0,5,26,28,25,27,24,29,14,16,13,15,12,17,50,52,49,51,48,53] : List (Fin 72)).getD i 0
private def pi31 (i : Fin 72) : Fin 72 := ([52,50,48,51,49,53,28,26,24,27,25,29,64,62,60,63,61,65,16,14,12,15,13,17,58,56,54,57,55,59,4,2,0,3,1,5,22,20,18,21,19,23,10,8,6,9,7,11,70,68,66,69,67,71,46,44,42,45,43,47,40,38,36,39,37,41,34,32,30,33,31,35] : List (Fin 72)).getD i 0
theorem sur31 : Function.Surjective p31 := by
  have h : ∀ i : Fin 72, p31 (pi31 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p33 (i : Fin 72) : Fin 72 := ([36,40,37,39,38,41,66,70,67,69,68,71,54,58,55,57,56,59,30,34,31,33,32,35,6,10,7,9,8,11,42,46,43,45,44,47,60,64,61,63,62,65,18,22,19,21,20,23,12,16,13,15,14,17,48,52,49,51,50,53,0,4,1,3,2,5,24,28,25,27,26,29] : List (Fin 72)).getD i 0
private def pi33 (i : Fin 72) : Fin 72 := ([60,62,64,63,61,65,24,26,28,27,25,29,48,50,52,51,49,53,42,44,46,45,43,47,66,68,70,69,67,71,18,20,22,21,19,23,0,2,4,3,1,5,30,32,34,33,31,35,54,56,58,57,55,59,12,14,16,15,13,17,36,38,40,39,37,41,6,8,10,9,7,11] : List (Fin 72)).getD i 0
theorem sur33 : Function.Surjective p33 := by
  have h : ∀ i : Fin 72, p33 (pi33 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p34 (i : Fin 72) : Fin 72 := ([19,22,20,21,18,23,43,46,44,45,42,47,31,34,32,33,30,35,25,28,26,27,24,29,1,4,2,3,0,5,61,64,62,63,60,65,67,70,68,69,66,71,49,52,50,51,48,53,7,10,8,9,6,11,37,40,38,39,36,41,13,16,14,15,12,17,55,58,56,57,54,59] : List (Fin 72)).getD i 0
private def pi34 (i : Fin 72) : Fin 72 := ([28,24,26,27,25,29,52,48,50,51,49,53,64,60,62,63,61,65,4,0,2,3,1,5,22,18,20,21,19,23,16,12,14,15,13,17,58,54,56,57,55,59,10,6,8,9,7,11,46,42,44,45,43,47,70,66,68,69,67,71,34,30,32,33,31,35,40,36,38,39,37,41] : List (Fin 72)).getD i 0
theorem sur34 : Function.Surjective p34 := by
  have h : ∀ i : Fin 72, p34 (pi34 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p35 (i : Fin 72) : Fin 72 := ([24,28,26,27,25,29,60,64,62,63,61,65,48,52,50,51,49,53,18,22,20,21,19,23,0,4,2,3,1,5,42,46,44,45,43,47,66,70,68,69,67,71,30,34,32,33,31,35,12,16,14,15,13,17,54,58,56,57,55,59,6,10,8,9,7,11,36,40,38,39,37,41] : List (Fin 72)).getD i 0
private def pi35 (i : Fin 72) : Fin 72 := ([24,28,26,27,25,29,60,64,62,63,61,65,48,52,50,51,49,53,18,22,20,21,19,23,0,4,2,3,1,5,42,46,44,45,43,47,66,70,68,69,67,71,30,34,32,33,31,35,12,16,14,15,13,17,54,58,56,57,55,59,6,10,8,9,7,11,36,40,38,39,37,41] : List (Fin 72)).getD i 0
theorem sur35 : Function.Surjective p35 := by
  have h : ∀ i : Fin 72, p35 (pi35 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p36 (i : Fin 72) : Fin 72 := ([67,66,70,69,68,71,55,54,58,57,56,59,37,36,40,39,38,41,61,60,64,63,62,65,43,42,46,45,44,47,49,48,52,51,50,53,13,12,16,15,14,17,25,24,28,27,26,29,31,30,34,33,32,35,7,6,10,9,8,11,19,18,22,21,20,23,1,0,4,3,2,5] : List (Fin 72)).getD i 0
private def pi36 (i : Fin 72) : Fin 72 := ([67,66,70,69,68,71,55,54,58,57,56,59,37,36,40,39,38,41,61,60,64,63,62,65,43,42,46,45,44,47,49,48,52,51,50,53,13,12,16,15,14,17,25,24,28,27,26,29,31,30,34,33,32,35,7,6,10,9,8,11,19,18,22,21,20,23,1,0,4,3,2,5] : List (Fin 72)).getD i 0
theorem sur36 : Function.Surjective p36 := by
  have h : ∀ i : Fin 72, p36 (pi36 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p38 (i : Fin 72) : Fin 72 := ([62,60,64,63,61,65,50,48,52,51,49,53,26,24,28,27,25,29,68,66,70,69,67,71,44,42,46,45,43,47,56,54,58,57,55,59,14,12,16,15,13,17,38,36,40,39,37,41,20,18,22,21,19,23,2,0,4,3,1,5,32,30,34,33,31,35,8,6,10,9,7,11] : List (Fin 72)).getD i 0
private def pi38 (i : Fin 72) : Fin 72 := ([55,58,54,57,56,59,67,70,66,69,68,71,37,40,36,39,38,41,49,52,48,51,50,53,13,16,12,15,14,17,61,64,60,63,62,65,43,46,42,45,44,47,25,28,24,27,26,29,7,10,6,9,8,11,31,34,30,33,32,35,1,4,0,3,2,5,19,22,18,21,20,23] : List (Fin 72)).getD i 0
theorem sur38 : Function.Surjective p38 := by
  have h : ∀ i : Fin 72, p38 (pi38 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p39 (i : Fin 72) : Fin 72 := ([44,43,46,45,42,47,32,31,34,33,30,35,20,19,22,21,18,23,68,67,70,69,66,71,62,61,64,63,60,65,38,37,40,39,36,41,8,7,10,9,6,11,56,55,58,57,54,59,26,25,28,27,24,29,2,1,4,3,0,5,50,49,52,51,48,53,14,13,16,15,12,17] : List (Fin 72)).getD i 0
private def pi39 (i : Fin 72) : Fin 72 := ([58,55,54,57,56,59,40,37,36,39,38,41,70,67,66,69,68,71,16,13,12,15,14,17,52,49,48,51,50,53,10,7,6,9,8,11,34,31,30,33,32,35,4,1,0,3,2,5,64,61,60,63,62,65,46,43,42,45,44,47,28,25,24,27,26,29,22,19,18,21,20,23] : List (Fin 72)).getD i 0
theorem sur39 : Function.Surjective p39 := by
  have h : ∀ i : Fin 72, p39 (pi39 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p40 (i : Fin 72) : Fin 72 := ([60,62,64,63,61,65,24,26,28,27,25,29,48,50,52,51,49,53,42,44,46,45,43,47,66,68,70,69,67,71,18,20,22,21,19,23,0,2,4,3,1,5,30,32,34,33,31,35,54,56,58,57,55,59,12,14,16,15,13,17,36,38,40,39,37,41,6,8,10,9,7,11] : List (Fin 72)).getD i 0
private def pi40 (i : Fin 72) : Fin 72 := ([36,40,37,39,38,41,66,70,67,69,68,71,54,58,55,57,56,59,30,34,31,33,32,35,6,10,7,9,8,11,42,46,43,45,44,47,60,64,61,63,62,65,18,22,19,21,20,23,12,16,13,15,14,17,48,52,49,51,50,53,0,4,1,3,2,5,24,28,25,27,26,29] : List (Fin 72)).getD i 0
theorem sur40 : Function.Surjective p40 := by
  have h : ∀ i : Fin 72, p40 (pi40 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p42 (i : Fin 72) : Fin 72 := ([66,67,68,71,70,69,60,61,62,65,64,63,42,43,44,47,46,45,54,55,56,59,58,57,36,37,38,41,40,39,48,49,50,53,52,51,24,25,26,29,28,27,12,13,14,17,16,15,30,31,32,35,34,33,18,19,20,23,22,21,6,7,8,11,10,9,0,1,2,5,4,3] : List (Fin 72)).getD i 0
private def pi42 (i : Fin 72) : Fin 72 := ([66,67,68,71,70,69,60,61,62,65,64,63,42,43,44,47,46,45,54,55,56,59,58,57,36,37,38,41,40,39,48,49,50,53,52,51,24,25,26,29,28,27,12,13,14,17,16,15,30,31,32,35,34,33,18,19,20,23,22,21,6,7,8,11,10,9,0,1,2,5,4,3] : List (Fin 72)).getD i 0
theorem sur42 : Function.Surjective p42 := by
  have h : ∀ i : Fin 72, p42 (pi42 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p44 (i : Fin 72) : Fin 72 := ([60,62,61,65,64,63,66,68,67,71,70,69,42,44,43,47,46,45,48,50,49,53,52,51,24,26,25,29,28,27,54,56,55,59,58,57,36,38,37,41,40,39,12,14,13,17,16,15,18,20,19,23,22,21,30,32,31,35,34,33,0,2,1,5,4,3,6,8,7,11,10,9] : List (Fin 72)).getD i 0
private def pi44 (i : Fin 72) : Fin 72 := ([60,62,61,65,64,63,66,68,67,71,70,69,42,44,43,47,46,45,48,50,49,53,52,51,24,26,25,29,28,27,54,56,55,59,58,57,36,38,37,41,40,39,12,14,13,17,16,15,18,20,19,23,22,21,30,32,31,35,34,33,0,2,1,5,4,3,6,8,7,11,10,9] : List (Fin 72)).getD i 0
theorem sur44 : Function.Surjective p44 := by
  have h : ∀ i : Fin 72, p44 (pi44 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p45 (i : Fin 72) : Fin 72 := ([43,44,42,47,46,45,67,68,66,71,70,69,61,62,60,65,64,63,31,32,30,35,34,33,19,20,18,23,22,21,37,38,36,41,40,39,55,56,54,59,58,57,7,8,6,11,10,9,25,26,24,29,28,27,49,50,48,53,52,51,1,2,0,5,4,3,13,14,12,17,16,15] : List (Fin 72)).getD i 0
private def pi45 (i : Fin 72) : Fin 72 := ([62,60,61,65,64,63,44,42,43,47,46,45,68,66,67,71,70,69,26,24,25,29,28,27,50,48,49,53,52,51,20,18,19,23,22,21,32,30,31,35,34,33,2,0,1,5,4,3,56,54,55,59,58,57,38,36,37,41,40,39,14,12,13,17,16,15,8,6,7,11,10,9] : List (Fin 72)).getD i 0
theorem sur45 : Function.Surjective p45 := by
  have h : ∀ i : Fin 72, p45 (pi45 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p46 (i : Fin 72) : Fin 72 := ([62,60,61,65,64,63,44,42,43,47,46,45,68,66,67,71,70,69,26,24,25,29,28,27,50,48,49,53,52,51,20,18,19,23,22,21,32,30,31,35,34,33,2,0,1,5,4,3,56,54,55,59,58,57,38,36,37,41,40,39,14,12,13,17,16,15,8,6,7,11,10,9] : List (Fin 72)).getD i 0
private def pi46 (i : Fin 72) : Fin 72 := ([43,44,42,47,46,45,67,68,66,71,70,69,61,62,60,65,64,63,31,32,30,35,34,33,19,20,18,23,22,21,37,38,36,41,40,39,55,56,54,59,58,57,7,8,6,11,10,9,25,26,24,29,28,27,49,50,48,53,52,51,1,2,0,5,4,3,13,14,12,17,16,15] : List (Fin 72)).getD i 0
theorem sur46 : Function.Surjective p46 := by
  have h : ∀ i : Fin 72, p46 (pi46 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
def p47 (i : Fin 72) : Fin 72 := ([44,43,42,47,46,45,62,61,60,65,64,63,68,67,66,71,70,69,20,19,18,23,22,21,32,31,30,35,34,33,26,25,24,29,28,27,50,49,48,53,52,51,2,1,0,5,4,3,38,37,36,41,40,39,56,55,54,59,58,57,8,7,6,11,10,9,14,13,12,17,16,15] : List (Fin 72)).getD i 0
private def pi47 (i : Fin 72) : Fin 72 := ([44,43,42,47,46,45,62,61,60,65,64,63,68,67,66,71,70,69,20,19,18,23,22,21,32,31,30,35,34,33,26,25,24,29,28,27,50,49,48,53,52,51,2,1,0,5,4,3,38,37,36,41,40,39,56,55,54,59,58,57,8,7,6,11,10,9,14,13,12,17,16,15] : List (Fin 72)).getD i 0
theorem sur47 : Function.Surjective p47 := by
  have h : ∀ i : Fin 72, p47 (pi47 i) = i := by decide +kernel
  exact fun i => ⟨_,h i⟩
end PEqualNP.Outside.Meta617

/- Checking the one-step tables and distinct live wires -/

namespace PEqualNP.Outside.Meta617
set_option maxHeartbeats 2000000
theorem cert0 : stepCheck 6 node0 tab0 = true := by decide +kernel
theorem uniq0 : node0.Nodup := by decide +kernel
theorem cert5 : stepCheck 6 node5 tab5 = true := by decide +kernel
theorem uniq5 : node5.Nodup := by decide +kernel
theorem cert10 : stepCheck 6 node10 tab10 = true := by decide +kernel
theorem uniq10 : node10.Nodup := by decide +kernel
theorem cert15 : stepCheck 7 node15 tab15 = true := by decide +kernel
theorem uniq15 : node15.Nodup := by decide +kernel
theorem cert20 : stepCheck 7 node20 tab20 = true := by decide +kernel
theorem uniq20 : node20.Nodup := by decide +kernel
theorem cert25 : stepCheck 7 node25 tab25 = true := by decide +kernel
theorem uniq25 : node25.Nodup := by decide +kernel
theorem cert30 : stepCheck 6 node30 tab30 = true := by decide +kernel
theorem uniq30 : node30.Nodup := by decide +kernel
theorem cert35 : stepCheck 7 node35 tab35 = true := by decide +kernel
theorem uniq35 : node35.Nodup := by decide +kernel
theorem cert40 : stepCheck 8 node40 tab40 = true := by decide +kernel
theorem uniq40 : node40.Nodup := by decide +kernel
end PEqualNP.Outside.Meta617

namespace PEqualNP.Outside.Meta617
set_option maxHeartbeats 2000000
theorem cert1 : stepCheck 6 node1 tab1 = true := by decide +kernel
theorem uniq1 : node1.Nodup := by decide +kernel
theorem cert6 : stepCheck 6 node6 tab6 = true := by decide +kernel
theorem uniq6 : node6.Nodup := by decide +kernel
theorem cert11 : stepCheck 7 node11 tab11 = true := by decide +kernel
theorem uniq11 : node11.Nodup := by decide +kernel
theorem cert16 : stepCheck 8 node16 tab16 = true := by decide +kernel
theorem uniq16 : node16.Nodup := by decide +kernel
theorem cert21 : stepCheck 7 node21 tab21 = true := by decide +kernel
theorem uniq21 : node21.Nodup := by decide +kernel
theorem cert26 : stepCheck 8 node26 tab26 = true := by decide +kernel
theorem uniq26 : node26.Nodup := by decide +kernel
theorem cert31 : stepCheck 7 node31 tab31 = true := by decide +kernel
theorem uniq31 : node31.Nodup := by decide +kernel
theorem cert36 : stepCheck 7 node36 tab36 = true := by decide +kernel
theorem uniq36 : node36.Nodup := by decide +kernel
theorem cert41 : stepCheck 7 node41 tab41 = true := by decide +kernel
theorem uniq41 : node41.Nodup := by decide +kernel
end PEqualNP.Outside.Meta617

namespace PEqualNP.Outside.Meta617
set_option maxHeartbeats 2000000
theorem cert2 : stepCheck 7 node2 tab2 = true := by decide +kernel
theorem uniq2 : node2.Nodup := by decide +kernel
theorem cert7 : stepCheck 6 node7 tab7 = true := by decide +kernel
theorem uniq7 : node7.Nodup := by decide +kernel
theorem cert12 : stepCheck 6 node12 tab12 = true := by decide +kernel
theorem uniq12 : node12.Nodup := by decide +kernel
theorem cert17 : stepCheck 6 node17 tab17 = true := by decide +kernel
theorem uniq17 : node17.Nodup := by decide +kernel
theorem cert22 : stepCheck 7 node22 tab22 = true := by decide +kernel
theorem uniq22 : node22.Nodup := by decide +kernel
theorem cert27 : stepCheck 6 node27 tab27 = true := by decide +kernel
theorem uniq27 : node27.Nodup := by decide +kernel
theorem cert32 : stepCheck 6 node32 tab32 = true := by decide +kernel
theorem uniq32 : node32.Nodup := by decide +kernel
theorem cert37 : stepCheck 6 node37 tab37 = true := by decide +kernel
theorem uniq37 : node37.Nodup := by decide +kernel
theorem cert42 : stepCheck 8 node42 tab42 = true := by decide +kernel
theorem uniq42 : node42.Nodup := by decide +kernel
end PEqualNP.Outside.Meta617

namespace PEqualNP.Outside.Meta617
set_option maxHeartbeats 2000000
theorem cert3 : stepCheck 6 node3 tab3 = true := by decide +kernel
theorem uniq3 : node3.Nodup := by decide +kernel
theorem cert8 : stepCheck 7 node8 tab8 = true := by decide +kernel
theorem uniq8 : node8.Nodup := by decide +kernel
theorem cert13 : stepCheck 7 node13 tab13 = true := by decide +kernel
theorem uniq13 : node13.Nodup := by decide +kernel
theorem cert18 : stepCheck 7 node18 tab18 = true := by decide +kernel
theorem uniq18 : node18.Nodup := by decide +kernel
theorem cert23 : stepCheck 7 node23 tab23 = true := by decide +kernel
theorem uniq23 : node23.Nodup := by decide +kernel
theorem cert28 : stepCheck 6 node28 tab28 = true := by decide +kernel
theorem uniq28 : node28.Nodup := by decide +kernel
theorem cert33 : stepCheck 6 node33 tab33 = true := by decide +kernel
theorem uniq33 : node33.Nodup := by decide +kernel
theorem cert38 : stepCheck 7 node38 tab38 = true := by decide +kernel
theorem uniq38 : node38.Nodup := by decide +kernel
theorem cert43 : stepCheck 8 node43 tab43 = true := by decide +kernel
theorem uniq43 : node43.Nodup := by decide +kernel
end PEqualNP.Outside.Meta617

namespace PEqualNP.Outside.Meta617
set_option maxHeartbeats 2000000
theorem cert4 : stepCheck 6 node4 tab4 = true := by decide +kernel
theorem uniq4 : node4.Nodup := by decide +kernel
theorem cert9 : stepCheck 7 node9 tab9 = true := by decide +kernel
theorem uniq9 : node9.Nodup := by decide +kernel
theorem cert14 : stepCheck 7 node14 tab14 = true := by decide +kernel
theorem uniq14 : node14.Nodup := by decide +kernel
theorem cert19 : stepCheck 6 node19 tab19 = true := by decide +kernel
theorem uniq19 : node19.Nodup := by decide +kernel
theorem cert24 : stepCheck 8 node24 tab24 = true := by decide +kernel
theorem uniq24 : node24.Nodup := by decide +kernel
theorem cert29 : stepCheck 6 node29 tab29 = true := by decide +kernel
theorem uniq29 : node29.Nodup := by decide +kernel
theorem cert34 : stepCheck 7 node34 tab34 = true := by decide +kernel
theorem uniq34 : node34.Nodup := by decide +kernel
theorem cert39 : stepCheck 7 node39 tab39 = true := by decide +kernel
theorem uniq39 : node39.Nodup := by decide +kernel
theorem cert44 : stepCheck 9 node44 tab44 = true := by decide +kernel
theorem uniq44 : node44.Nodup := by decide +kernel
end PEqualNP.Outside.Meta617

/- Checking the images of concrete wire signatures -/

namespace PEqualNP.Outside.Meta617
set_option maxHeartbeats 2000000
theorem mv0_mw0q41041041041041041 : relWord p0 mw0q41041041041041041 = mw0q41041041041041041 := by decide +kernel
theorem mv0_mw3ffffq0 : relWord p0 mw3ffffq0 = mw3ffffq0 := by decide +kernel
theorem mv0_mw3fffffffqf3cf3cf3cf3cf3cf3c : relWord p0 mw3fffffffqf3cf3cf3cf3cf3cf3c = mw3fffffffqf3cf3cf3cf3cf3cf3c := by decide +kernel
theorem mv0_mwfc0fc0fc0000q249249249249249249 : relWord p0 mwfc0fc0fc0000q249249249249249249 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv0_mwffffc0fc0ffffffqe79e79e79e79e79e79 : relWord p0 mwffffc0fc0ffffffqe79e79e79e79e79e79 = mwffffc0fc0ffffffqe79e79e79e79e79e79 := by decide +kernel
theorem mv0_mwfc0fc003f00000003fq30c30c30c30c30c30c : relWord p0 mwfc0fc003f00000003fq30c30c30c30c30c30c = mwfc0fc003f00000003fq30c30c30c30c30c30c := by decide +kernel
theorem mv0_mwfff000fc0000fc0000qc30c30c30c30c30c30 : relWord p0 mwfff000fc0000fc0000qc30c30c30c30c30c30 = mwfff000fc0000fc0000qc30c30c30c30c30c30 := by decide +kernel
theorem mv1_mw3ffffq618618618618618618 : relWord p1 mw3ffffq618618618618618618 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv1_mwfc0fc0fc0000q249249249249249249 : relWord p1 mwfc0fc0fc0000q249249249249249249 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv1_mwfff00003fffffffqf7df7df7df7df7df7d : relWord p1 mwfff00003fffffffqf7df7df7df7df7df7d = mw3ffffffffffqfbefbefbefbefbefbe := by decide +kernel
theorem mv1_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p1 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv2_mw3ffc003fq924924924924924924 : relWord p2 mw3ffc003fq924924924924924924 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv2_mwfff00000003f000q861861861861861861 : relWord p2 mwfff00000003f000q861861861861861861 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv2_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p2 mwfff000fc0000000000qc30c30c30c30c30c30 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv3_mw3ffffq618618618618618618 : relWord p3 mw3ffffq618618618618618618 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv3_mwfc0fc0fc003fq249249249249249249 : relWord p3 mwfc0fc0fc003fq249249249249249249 = mwfc0fc003f000000fc0q30c30c30c30c30c30c := by decide +kernel
theorem mv3_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p3 mwfc0fc003f000000000q30c30c30c30c30c30c = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv4_mw0q30c30c30c30c30c30c : relWord p4 mw0q30c30c30c30c30c30c = mw0q249249249249249249 := by decide +kernel
theorem mv4_mwfc0fc0fc0000q249249249249249249 : relWord p4 mwfc0fc0fc0000q249249249249249249 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv4_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p4 mw3f03f00003f000000q28a28a28a28a28a28a = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv4_mwfc0fc003f03ffc003fqb2cb2cb2cb2cb2cb2c : relWord p4 mwfc0fc003f03ffc003fqb2cb2cb2cb2cb2cb2c = mwffffc0fc0fff000qa69a69a69a69a69a69 := by decide +kernel
theorem mv6_mw0q820820820820820820 : relWord p6 mw0q820820820820820820 = mw0q208208208208208208 := by decide +kernel
theorem mv6_mw3ffc003fqb2cb2cb2cb2cb2cb2c : relWord p6 mw3ffc003fqb2cb2cb2cb2cb2cb2c = mw3ffffqe38e38e38e38e38e38 := by decide +kernel
theorem mv6_mwfc0fffffffffqf7df7df7df7df7df7d : relWord p6 mwfc0fffffffffqf7df7df7df7df7df7d = mw3ffffffffffqfbefbefbefbefbefbe := by decide +kernel
theorem mv6_mw3f03f03fffffc0fffqbaebaebaebaebaebae : relWord p6 mw3f03f03fffffc0fffqbaebaebaebaebaebae = mwffffc0fc0ffffffqe79e79e79e79e79e79 := by decide +kernel
theorem mv6_mwfc0fc003f00003ffffq71c71c71c71c71c71c : relWord p6 mwfc0fc003f00003ffffq71c71c71c71c71c71c = mwfff000fc003ffc003fqd34d34d34d34d34d34 := by decide +kernel
theorem mv7_mw3ffffq618618618618618618 : relWord p7 mw3ffffq618618618618618618 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv7_mw3ffc0000fffq8a28a28a28a28a28a2 : relWord p7 mw3ffc0000fffq8a28a28a28a28a28a2 = mw3f03f00003f00003fq28a28a28a28a28a28a := by decide +kernel
theorem mv7_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p7 mw3f03f00003f000000q28a28a28a28a28a28a = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv7_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p7 mwfff000fc0000000000qc30c30c30c30c30c30 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv8_mw3ffc003fq924924924924924924 : relWord p8 mw3ffc003fq924924924924924924 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv8_mwfc0fc0fc0000q249249249249249249 : relWord p8 mwfc0fc0fc0000q249249249249249249 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv8_mw3f03f00003f000fffq28a28a28a28a28a28a : relWord p8 mw3f03f00003f000fffq28a28a28a28a28a28a = mwfff000fc0000fc003fqc30c30c30c30c30c30 := by decide +kernel
theorem mv9_mw3f000q820820820820820820 : relWord p9 mw3f000q820820820820820820 = mw3fq208208208208208208 := by decide +kernel
theorem mv9_mw3fffffc0fffq9a69a69a69a69a69a6 : relWord p9 mw3fffffc0fffq9a69a69a69a69a69a6 = mw3f03ffc0ffffc0000q2cb2cb2cb2cb2cb2cb := by decide +kernel
theorem mv9_mwfc0fc0ffffffq659659659659659659 : relWord p9 mwfc0fc0ffffffq659659659659659659 = mwfff000fc003ffc003fqd34d34d34d34d34d34 := by decide +kernel
theorem mv9_mwffffc0fc0fff000qa69a69a69a69a69a69 : relWord p9 mwffffc0fc0fff000qa69a69a69a69a69a69 = mwfff000fc000003ffffqe38e38e38e38e38e38 := by decide +kernel
theorem mv9_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p9 mwfff000fc0000000000qc30c30c30c30c30c30 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv10_mw3ffffq618618618618618618 : relWord p10 mw3ffffq618618618618618618 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv10_mwfc0fc0fc0000q249249249249249249 : relWord p10 mwfc0fc0fc0000q249249249249249249 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv10_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p10 mwfc0fc003f000000000q30c30c30c30c30c30c = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv11_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p11 mw3ffc0000fc0q8a28a28a28a28a28a2 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv11_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p11 mw3f03f00003f000000q28a28a28a28a28a28a = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv12_mw3ffc003fq924924924924924924 : relWord p12 mw3ffc003fq924924924924924924 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv12_mwfc0fc0fc0000q249249249249249249 : relWord p12 mwfc0fc0fc0000q249249249249249249 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv12_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p12 mw3f03f00003f000000q28a28a28a28a28a28a = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv13_mw3ffffq618618618618618618 : relWord p13 mw3ffffq618618618618618618 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv13_mw3f000000000000q0 : relWord p13 mw3f000000000000q0 = mw3fq0 := by decide +kernel
theorem mv13_mw3f03ffc0ffffc0000q2cb2cb2cb2cb2cb2cb : relWord p13 mw3f03ffc0ffffc0000q2cb2cb2cb2cb2cb2cb = mwfff000fc003ffc003fqd34d34d34d34d34d34 := by decide +kernel
theorem mv14_mw3ffffq618618618618618618 : relWord p14 mw3ffffq618618618618618618 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv14_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p14 mw3ffc0000fc0q8a28a28a28a28a28a2 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv14_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p14 mw3f03f00003f000000q28a28a28a28a28a28a = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv15_mw3f000000q0 : relWord p15 mw3f000000q0 = mw3fq0 := by decide +kernel
theorem mv15_mwfc0fc0fc0000q249249249249249249 : relWord p15 mwfc0fc0fc0000q249249249249249249 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv15_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p15 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv16_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p16 mw3ffc0000fc0q8a28a28a28a28a28a2 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv16_mwffffc0fc0fff000qa69a69a69a69a69a69 : relWord p16 mwffffc0fc0fff000qa69a69a69a69a69a69 = mwfff000fc000003ffffqe38e38e38e38e38e38 := by decide +kernel
theorem mv16_mwfc0fc0ffffc0fc0000q34d34d34d34d34d34d : relWord p16 mwfc0fc0ffffc0fc0000q34d34d34d34d34d34d = mwfff000fc003ffc003fqd34d34d34d34d34d34 := by decide +kernel
theorem mv17_mw3ffc003fq924924924924924924 : relWord p17 mw3ffc003fq924924924924924924 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv17_mwfc0fc0fc0000q249249249249249249 : relWord p17 mwfc0fc0fc0000q249249249249249249 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv17_mwfc0fc003ffc0000fc0qbaebaebaebaebaebae : relWord p17 mwfc0fc003ffc0000fc0qbaebaebaebaebaebae = mw3fffffffqf3cf3cf3cf3cf3cf3c := by decide +kernel
theorem mv18_mw3ffc003fq924924924924924924 : relWord p18 mw3ffc003fq924924924924924924 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv18_mwfffffffc0fffqbefbefbefbefbefbef : relWord p18 mwfffffffc0fffqbefbefbefbefbefbef = mw3ffffffffffqfbefbefbefbefbefbe := by decide +kernel
theorem mv18_mwffffc0fc0fff000qa69a69a69a69a69a69 : relWord p18 mwffffc0fc0fff000qa69a69a69a69a69a69 = mwfff000fc000003ffffqe38e38e38e38e38e38 := by decide +kernel
theorem mv18_mwfff000fc000003ffffqe38e38e38e38e38e38 : relWord p18 mwfff000fc000003ffffqe38e38e38e38e38e38 = mwffffc0fc0fff000qa69a69a69a69a69a69 := by decide +kernel
theorem mv19_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p19 mw3ffc0000fc0q8a28a28a28a28a28a2 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv19_mwfff00000003f000q861861861861861861 : relWord p19 mwfff00000003f000q861861861861861861 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv19_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p19 mwfff000fc0000000000qc30c30c30c30c30c30 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv20_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p20 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv20_mwfff00000003f03fq861861861861861861 : relWord p20 mwfff00000003f03fq861861861861861861 = mwfff000fc0000fc0000qc30c30c30c30c30c30 := by decide +kernel
theorem mv20_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p20 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv21_mw3f000000q208208208208208208 : relWord p21 mw3f000000q208208208208208208 = mw3fq208208208208208208 := by decide +kernel
theorem mv21_mw3ffc003ffffqebaebaebaebaebaeba : relWord p21 mw3ffc003ffffqebaebaebaebaebaeba = mwfff000fc0fc0fc0000qe79e79e79e79e79e79 := by decide +kernel
theorem mv21_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p21 mw3f03f00003f000000q28a28a28a28a28a28a = mw3ffffq618618618618618618 := by decide +kernel
theorem mv21_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p21 mwfff000fc0000000000qc30c30c30c30c30c30 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv22_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p22 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv22_mwfc0000000000000q208208208208208208 : relWord p22 mwfc0000000000000q208208208208208208 = mw3fq208208208208208208 := by decide +kernel
theorem mv22_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p22 mwfc0fc003f000000000q30c30c30c30c30c30c = mw3ffffq618618618618618618 := by decide +kernel
theorem mv23_mw3ffc003fq924924924924924924 : relWord p23 mw3ffc003fq924924924924924924 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv23_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p23 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv23_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p23 mw3f03f00003f000000q28a28a28a28a28a28a = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv23_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p23 mwfff000fc0000000000qc30c30c30c30c30c30 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv24_mw3ffc003fq924924924924924924 : relWord p24 mw3ffc003fq924924924924924924 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv24_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p24 mw3f03f00003f000000q28a28a28a28a28a28a = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv25_mw3ffffq618618618618618618 : relWord p25 mw3ffffq618618618618618618 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv25_mwfff00000003f000q861861861861861861 : relWord p25 mwfff00000003f000q861861861861861861 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv25_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p25 mwfff000fc0000000000qc30c30c30c30c30c30 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv28_mwfc0fc0fc0000q249249249249249249 : relWord p28 mwfc0fc0fc0000q249249249249249249 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv28_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p28 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv28_mwfff000fc003fffffffqf3cf3cf3cf3cf3cf3c : relWord p28 mwfff000fc003fffffffqf3cf3cf3cf3cf3cf3c = mwffffc0fc0ffffffqe79e79e79e79e79e79 := by decide +kernel
theorem mv30_mwfc0fc0fc0000q249249249249249249 : relWord p30 mwfc0fc0fc0000q249249249249249249 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv30_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p30 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv31_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p31 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv31_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p31 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv33_mw3ffc003fq924924924924924924 : relWord p33 mw3ffc003fq924924924924924924 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv33_mwfc0ffffc003fqb6db6db6db6db6db6d : relWord p33 mwfc0ffffc003fqb6db6db6db6db6db6d = mwfff000fc0fc0fc0000qe79e79e79e79e79e79 := by decide +kernel
theorem mv33_mwfc0fc003f000000000q34d34d34d34d34d34d : relWord p33 mwfc0fc003f000000000q34d34d34d34d34d34d = mw3ffffq659659659659659659 := by decide +kernel
theorem mv34_mw3ffffq618618618618618618 : relWord p34 mw3ffffq618618618618618618 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv34_mwfff00000003f000q861861861861861861 : relWord p34 mwfff00000003f000q861861861861861861 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv34_mwfff000fc003ffc003fqd34d34d34d34d34d34 : relWord p34 mwfff000fc003ffc003fqd34d34d34d34d34d34 = mw3fffffc0fffq9a69a69a69a69a69a6 := by decide +kernel
theorem mv35_mw3fffffc0fffq9a69a69a69a69a69a6 : relWord p35 mw3fffffc0fffq9a69a69a69a69a69a6 = mwfff000fc003ffc003fqd34d34d34d34d34d34 := by decide +kernel
theorem mv35_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p35 mw3f03f00003f000000q28a28a28a28a28a28a = mw3ffffq618618618618618618 := by decide +kernel
theorem mv35_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p35 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv36_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p36 mw3ffc0000fc0q8a28a28a28a28a28a2 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv36_mwfc0000000000000000q0 : relWord p36 mwfc0000000000000000q0 = mw3fq0 := by decide +kernel
theorem mv38_mw3ffffq618618618618618618 : relWord p38 mw3ffffq618618618618618618 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv38_mwfff00000003f000q861861861861861861 : relWord p38 mwfff00000003f000q861861861861861861 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv38_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p38 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv39_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p39 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv39_mwffffc0fc0fff000qa69a69a69a69a69a69 : relWord p39 mwffffc0fc0fff000qa69a69a69a69a69a69 = mwfff000fc000003ffffqe38e38e38e38e38e38 := by decide +kernel
theorem mv39_mwfff000fc0fc0fc0000qe79e79e79e79e79e79 : relWord p39 mwfff000fc0fc0fc0000qe79e79e79e79e79e79 = mw3fffffffqf3cf3cf3cf3cf3cf3c := by decide +kernel
theorem mv40_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p40 mw3ffc0000fc0q8a28a28a28a28a28a2 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv40_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p40 mwfc0fc003f000000000q30c30c30c30c30c30c = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv42_mw3ffc003fq924924924924924924 : relWord p42 mw3ffc003fq924924924924924924 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv42_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p42 mw3f03f00003f000000q28a28a28a28a28a28a = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv42_mwfff000fc0000000000qe38e38e38e38e38e38 : relWord p42 mwfff000fc0000000000qe38e38e38e38e38e38 = mw3ffffqe38e38e38e38e38e38 := by decide +kernel
theorem mv44_mwfc0fc0fc0000q249249249249249249 : relWord p44 mwfc0fc0fc0000q249249249249249249 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv44_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p44 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv45_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p45 mw3ffc0000fc0q8a28a28a28a28a28a2 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv45_mwfff00000003f03fq861861861861861861 : relWord p45 mwfff00000003f03fq861861861861861861 = mwffffc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv45_mwfff000fc003ffc003fqd34d34d34d34d34d34 : relWord p45 mwfff000fc003ffc003fqd34d34d34d34d34d34 = mw3f03f00003f03ffffq69a69a69a69a69a69a := by decide +kernel
theorem mv46_mwfc0fc0fc0000q249249249249249249 : relWord p46 mwfc0fc0fc0000q249249249249249249 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv46_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p46 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv47_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p47 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv47_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p47 mw3f03f00003f000000q28a28a28a28a28a28a = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
end PEqualNP.Outside.Meta617

namespace PEqualNP.Outside.Meta617
set_option maxHeartbeats 2000000
theorem mv0_mw0q208208208208208208 : relWord p0 mw0q208208208208208208 = mw0q208208208208208208 := by decide +kernel
theorem mv0_mw3ffffq618618618618618618 : relWord p0 mw3ffffq618618618618618618 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv0_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p0 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv0_mwfff00000003f000q861861861861861861 : relWord p0 mwfff00000003f000q861861861861861861 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv0_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p0 mw3f03f00003f000000q28a28a28a28a28a28a = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv0_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p0 mwfff000fc0000000000qc30c30c30c30c30c30 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv0_mwfff000fc003ffc003fqd34d34d34d34d34d34 : relWord p0 mwfff000fc003ffc003fqd34d34d34d34d34d34 = mwfff000fc003ffc003fqd34d34d34d34d34d34 := by decide +kernel
theorem mv1_mw3ffc003fq924924924924924924 : relWord p1 mw3ffc003fq924924924924924924 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv1_mwfc0fc0fc003fq249249249249249249 : relWord p1 mwfc0fc0fc003fq249249249249249249 = mw3f03f00003f00003fq28a28a28a28a28a28a := by decide +kernel
theorem mv1_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p1 mw3f03f00003f000000q28a28a28a28a28a28a = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv1_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p1 mwfff000fc0000000000qc30c30c30c30c30c30 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv2_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p2 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv2_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p2 mw3f03f00003f000000q28a28a28a28a28a28a = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv2_mwfff000fc000000003fqc30c30c30c30c30c30 : relWord p2 mwfff000fc000000003fqc30c30c30c30c30c30 = mwfff000fc0000000fc0qc30c30c30c30c30c30 := by decide +kernel
theorem mv3_mw3ffc003fq924924924924924924 : relWord p3 mw3ffc003fq924924924924924924 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv3_mwfff00000003f000q861861861861861861 : relWord p3 mwfff00000003f000q861861861861861861 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv3_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p3 mwfff000fc0000000000qc30c30c30c30c30c30 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv4_mw3ffffq618618618618618618 : relWord p4 mw3ffffq618618618618618618 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv4_mwfc0fc0fc003fq249249249249249249 : relWord p4 mwfc0fc0fc003fq249249249249249249 = mw3f03f00003f03f000q28a28a28a28a28a28a := by decide +kernel
theorem mv4_mw3f03f00003f00003fq28a28a28a28a28a28a : relWord p4 mw3f03f00003f00003fq28a28a28a28a28a28a = mwfc0fc003f00003f000q30c30c30c30c30c30c := by decide +kernel
theorem mv4_mwfc0fc003f03fffffffqf3cf3cf3cf3cf3cf3c : relWord p4 mwfc0fc003f03fffffffqf3cf3cf3cf3cf3cf3c = mwffffc0fc0ffffffqe79e79e79e79e79e79 := by decide +kernel
theorem mv6_mw3fq0 : relWord p6 mw3fq0 = mw3fq0 := by decide +kernel
theorem mv6_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p6 mw3ffc0000fc0q8a28a28a28a28a28a2 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv6_mwfff00000003f000q861861861861861861 : relWord p6 mwfff00000003f000q861861861861861861 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv6_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p6 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv6_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p6 mwfff000fc0000000000qc30c30c30c30c30c30 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv7_mw3ffc003fq924924924924924924 : relWord p7 mw3ffc003fq924924924924924924 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv7_mwfc0fc0fc0000q249249249249249249 : relWord p7 mwfc0fc0fc0000q249249249249249249 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv7_mw3f03f00003f03ffffq69a69a69a69a69a69a : relWord p7 mw3f03f00003f03ffffq69a69a69a69a69a69a = mw3fffffc0fffq9a69a69a69a69a69a6 := by decide +kernel
theorem mv7_mwfff000fc000000003fqc30c30c30c30c30c30 : relWord p7 mwfff000fc000000003fqc30c30c30c30c30c30 = mwfc0fc003f00000003fq30c30c30c30c30c30c := by decide +kernel
theorem mv8_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p8 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv8_mwfff00000003f000q861861861861861861 : relWord p8 mwfff00000003f000q861861861861861861 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv8_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p8 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv9_mw3ffffq618618618618618618 : relWord p9 mw3ffffq618618618618618618 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv9_mwfc0fc0fc0000q249249249249249249 : relWord p9 mwfc0fc0fc0000q249249249249249249 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv9_mwfff00000003f000q861861861861861861 : relWord p9 mwfff00000003f000q861861861861861861 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv9_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p9 mw3f03f00003f000000q28a28a28a28a28a28a = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv9_mwfff000fc0000fc0000qc30c30c30c30c30c30 : relWord p9 mwfff000fc0000fc0000qc30c30c30c30c30c30 = mwfc0fc0fff000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv10_mw3ffc003fq924924924924924924 : relWord p10 mw3ffc003fq924924924924924924 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv10_mwfff00000003f000q861861861861861861 : relWord p10 mwfff00000003f000q861861861861861861 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv10_mwfc0fc003f00003ffffq71c71c71c71c71c71c : relWord p10 mwfc0fc003f00003ffffq71c71c71c71c71c71c = mw3fffffc0fffq9a69a69a69a69a69a6 := by decide +kernel
theorem mv11_mwfc0fc0fc0000q249249249249249249 : relWord p11 mwfc0fc0fc0000q249249249249249249 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv11_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p11 mwfc0fc003f000000000q30c30c30c30c30c30c = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv12_mwfc0000000q0 : relWord p12 mwfc0000000q0 = mw3fq0 := by decide +kernel
theorem mv12_mwffffc0fc0fc0qaebaebaebaebaebaeb : relWord p12 mwffffc0fc0fc0qaebaebaebaebaebaeb = mw3fffffffqf3cf3cf3cf3cf3cf3c := by decide +kernel
theorem mv12_mw3f03f00003f00003fq28a28a28a28a28a28a : relWord p12 mw3f03f00003f00003fq28a28a28a28a28a28a = mwfff000fc0fc0000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv13_mw3ffc003fq924924924924924924 : relWord p13 mw3ffc003fq924924924924924924 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv13_mwfff00000003f000q861861861861861861 : relWord p13 mwfff00000003f000q861861861861861861 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv13_mw3ffff00003f03f000qaebaebaebaebaebaeb : relWord p13 mw3ffff00003f03f000qaebaebaebaebaebaeb = mw3fffffffqf3cf3cf3cf3cf3cf3c := by decide +kernel
theorem mv14_mwfc0000q0 : relWord p14 mwfc0000q0 = mw3fq0 := by decide +kernel
theorem mv14_mwfc0fc0fc0000q249249249249249249 : relWord p14 mwfc0fc0fc0000q249249249249249249 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv14_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p14 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv15_mw3f000000q82082082082082082 : relWord p15 mw3f000000q82082082082082082 = mw3fq104104104104104104 := by decide +kernel
theorem mv15_mwfff00000003f000q861861861861861861 : relWord p15 mwfff00000003f000q861861861861861861 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv15_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p15 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv16_mwfc0fc0fc0000q249249249249249249 : relWord p16 mwfc0fc0fc0000q249249249249249249 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv16_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p16 mw3f03f00003f000000q28a28a28a28a28a28a = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv16_mwfc0fff03f00003f000qb6db6db6db6db6db6d : relWord p16 mwfc0fff03f00003f000qb6db6db6db6db6db6d = mw3fffffffqf3cf3cf3cf3cf3cf3c := by decide +kernel
theorem mv17_mw3f000000000q0 : relWord p17 mw3f000000000q0 = mw3fq0 := by decide +kernel
theorem mv17_mwfff00000003f000q861861861861861861 : relWord p17 mwfff00000003f000q861861861861861861 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv17_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p17 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv18_mwfc0fc0000q0 : relWord p18 mwfc0fc0000q0 = mwfffq0 := by decide +kernel
theorem mv18_mwfff00000003f000q861861861861861861 : relWord p18 mwfff00000003f000q861861861861861861 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv18_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p18 mw3f03f00003f000000q28a28a28a28a28a28a = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv18_mwfff000fffffffc0fffqdb6db6db6db6db6db6 : relWord p18 mwfff000fffffffc0fffqdb6db6db6db6db6db6 = mwfff03ffffffffffq9e79e79e79e79e79e7 := by decide +kernel
theorem mv19_mw3fffffc0fffq9a69a69a69a69a69a6 : relWord p19 mw3fffffc0fffq9a69a69a69a69a69a6 = mwfff000ffffc0000fc0qcb2cb2cb2cb2cb2cb2 := by decide +kernel
theorem mv19_mwfff03ffc003ffc0q8e38e38e38e38e38e3 : relWord p19 mwfff03ffc003ffc0q8e38e38e38e38e38e3 = mwfff000fc003ffc003fqd34d34d34d34d34d34 := by decide +kernel
theorem mv20_mw3ffffq618618618618618618 : relWord p20 mw3ffffq618618618618618618 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv20_mwfc0fc0fc0000q249249249249249249 : relWord p20 mwfc0fc0fc0000q249249249249249249 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv20_mwfff00003ffff03fq965965965965965965 : relWord p20 mwfff00003ffff03fq965965965965965965 = mwfff000fc003ffc003fqd34d34d34d34d34d34 := by decide +kernel
theorem mv20_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p20 mwfff000fc0000000000qc30c30c30c30c30c30 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv21_mw3ffc003fq924924924924924924 : relWord p21 mw3ffc003fq924924924924924924 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv21_mw3fffffc0fffq9a69a69a69a69a69a6 : relWord p21 mw3fffffc0fffq9a69a69a69a69a69a6 = mwfff000fc003ffc003fqd34d34d34d34d34d34 := by decide +kernel
theorem mv21_mw3f03f00003f00003fq28a28a28a28a28a28a : relWord p21 mw3f03f00003f00003fq28a28a28a28a28a28a = mwffffffq618618618618618618 := by decide +kernel
theorem mv22_mw3ffffq618618618618618618 : relWord p22 mw3ffffq618618618618618618 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv22_mw3fffffc0fffq9a69a69a69a69a69a6 : relWord p22 mw3fffffc0fffq9a69a69a69a69a69a6 = mwfff000ffffc0000fc0qcb2cb2cb2cb2cb2cb2 := by decide +kernel
theorem mv22_mwfff00000003f000q861861861861861861 : relWord p22 mwfff00000003f000q861861861861861861 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv22_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p22 mwfff000fc0000000000qc30c30c30c30c30c30 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv23_mw3ffc0fffq924924924924924924 : relWord p23 mw3ffc0fffq924924924924924924 = mwfff000fc0000fc0000qc30c30c30c30c30c30 := by decide +kernel
theorem mv23_mw3fffffc0fffq9a69a69a69a69a69a6 : relWord p23 mw3fffffc0fffq9a69a69a69a69a69a6 = mwfff000fc003ffc003fqd34d34d34d34d34d34 := by decide +kernel
theorem mv23_mw3f03f00003f00003fq28a28a28a28a28a28a : relWord p23 mw3f03f00003f00003fq28a28a28a28a28a28a = mwfc0fc0fff000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv23_mwfff000fc003ffc003fqd34d34d34d34d34d34 : relWord p23 mwfff000fc003ffc003fqd34d34d34d34d34d34 = mwfffffffc000003f000qc71c71c71c71c71c71 := by decide +kernel
theorem mv24_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p24 mw3ffc0000fc0q8a28a28a28a28a28a2 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv24_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p24 mwfc0fc003f000000000q30c30c30c30c30c30c = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv25_mw3ffc003fq924924924924924924 : relWord p25 mw3ffc003fq924924924924924924 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv25_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p25 mw3f03f00003f000000q28a28a28a28a28a28a = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv28_mw3ffffq618618618618618618 : relWord p28 mw3ffffq618618618618618618 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv28_mwfff00000003f000q861861861861861861 : relWord p28 mwfff00000003f000q861861861861861861 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv28_mwfc0fc003f00003ffffq71c71c71c71c71c71c : relWord p28 mwfc0fc003f00003ffffq71c71c71c71c71c71c = mwfffffffc000003f000qc71c71c71c71c71c71 := by decide +kernel
theorem mv30_mw3ffffq618618618618618618 : relWord p30 mw3ffffq618618618618618618 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv30_mwfff00000003f000q861861861861861861 : relWord p30 mwfff00000003f000q861861861861861861 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv30_mwfffffffc000003f000qc71c71c71c71c71c71 : relWord p30 mwfffffffc000003f000qc71c71c71c71c71c71 = mw3fffffc0fffq9a69a69a69a69a69a6 := by decide +kernel
theorem mv31_mwfc0fc0fc0000q249249249249249249 : relWord p31 mwfc0fc0fc0000q249249249249249249 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv31_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p31 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv33_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p33 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv33_mwfff00000003f000q861861861861861861 : relWord p33 mwfff00000003f000q861861861861861861 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv33_mwfc0fffffffc0fff000qb6db6db6db6db6db6d : relWord p33 mwfc0fffffffc0fff000qb6db6db6db6db6db6d = mwffffc0fc0ffffffqe79e79e79e79e79e79 := by decide +kernel
theorem mv34_mw3ffc003fq924924924924924924 : relWord p34 mw3ffc003fq924924924924924924 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv34_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p34 mw3f03f00003f000000q28a28a28a28a28a28a = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv35_mw3ffffq618618618618618618 : relWord p35 mw3ffffq618618618618618618 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv35_mwfc0fc0fc0000q249249249249249249 : relWord p35 mwfc0fc0fc0000q249249249249249249 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv35_mw3f03f00003f000000q2cb2cb2cb2cb2cb2cb : relWord p35 mw3f03f00003f000000q2cb2cb2cb2cb2cb2cb = mw3ffffq659659659659659659 := by decide +kernel
theorem mv35_mwfff000ffffc0000fc0qcb2cb2cb2cb2cb2cb2 : relWord p35 mwfff000ffffc0000fc0qcb2cb2cb2cb2cb2cb2 = mwfff000ffffc0000fc0qcb2cb2cb2cb2cb2cb2 := by decide +kernel
theorem mv36_mwfc0fc0fc0000q249249249249249249 : relWord p36 mwfc0fc0fc0000q249249249249249249 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv36_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p36 mwfc0fc003f000000000q30c30c30c30c30c30c = mw3ffffq618618618618618618 := by decide +kernel
theorem mv38_mw3ffc003fq924924924924924924 : relWord p38 mw3ffc003fq924924924924924924 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv38_mw3f000000000000000q0 : relWord p38 mw3f000000000000000q0 = mw3fq0 := by decide +kernel
theorem mv38_mwfff03ffc003f000000qebaebaebaebaebaeba : relWord p38 mwfff03ffc003f000000qebaebaebaebaebaeba = mw3fffffffqf3cf3cf3cf3cf3cf3c := by decide +kernel
theorem mv39_mwfc0000000000q0 : relWord p39 mwfc0000000000q0 = mw3fq0 := by decide +kernel
theorem mv39_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p39 mw3f03f00003f000000q28a28a28a28a28a28a = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv39_mwfffffffc000003f000qc71c71c71c71c71c71 : relWord p39 mwfffffffc000003f000qc71c71c71c71c71c71 = mwfff000fc003ffc003fqd34d34d34d34d34d34 := by decide +kernel
theorem mv40_mwfc0fc0fc0000q249249249249249249 : relWord p40 mwfc0fc0fc0000q249249249249249249 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv40_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p40 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv42_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p42 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv42_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p42 mwfc0fc003f000000000q30c30c30c30c30c30c = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv42_mwfffffffc0fc0fff000qe79e79e79e79e79e79 : relWord p42 mwfffffffc0fc0fff000qe79e79e79e79e79e79 = mwffffc0fc0ffffffqe79e79e79e79e79e79 := by decide +kernel
theorem mv44_mwfff00000003f000q861861861861861861 : relWord p44 mwfff00000003f000q861861861861861861 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv44_mwfff000fc003ffc003fqd34d34d34d34d34d34 : relWord p44 mwfff000fc003ffc003fqd34d34d34d34d34d34 = mw3f03f00003f03ffffq69a69a69a69a69a69a := by decide +kernel
theorem mv45_mwfc0000000000q820820820820820820 : relWord p45 mwfc0000000000q820820820820820820 = mw3fq208208208208208208 := by decide +kernel
theorem mv45_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p45 mw3f03f00003f000000q28a28a28a28a28a28a = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv46_mw3ffc003fq924924924924924924 : relWord p46 mw3ffc003fq924924924924924924 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv46_mwfff00000003f000q861861861861861861 : relWord p46 mwfff00000003f000q861861861861861861 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv46_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p46 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv47_mwfc0fc0fc0000q249249249249249249 : relWord p47 mwfc0fc0fc0000q249249249249249249 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv47_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p47 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfff00000003f000q861861861861861861 := by decide +kernel
end PEqualNP.Outside.Meta617

namespace PEqualNP.Outside.Meta617
set_option maxHeartbeats 2000000
theorem mv0_mw3fq0 : relWord p0 mw3fq0 = mw3fq0 := by decide +kernel
theorem mv0_mw3ffffq659659659659659659 : relWord p0 mw3ffffq659659659659659659 = mw3ffffq659659659659659659 := by decide +kernel
theorem mv0_mw3fffffc0fffq9a69a69a69a69a69a6 : relWord p0 mw3fffffc0fffq9a69a69a69a69a69a6 = mw3fffffc0fffq9a69a69a69a69a69a6 := by decide +kernel
theorem mv0_mwfff03ffffffffffq9e79e79e79e79e79e7 : relWord p0 mwfff03ffffffffffq9e79e79e79e79e79e7 = mwfff03ffffffffffq9e79e79e79e79e79e7 := by decide +kernel
theorem mv0_mw3f03f00003f00003fq28a28a28a28a28a28a : relWord p0 mw3f03f00003f00003fq28a28a28a28a28a28a = mw3f03f00003f00003fq28a28a28a28a28a28a := by decide +kernel
theorem mv0_mwfff000fc000000003fqc30c30c30c30c30c30 : relWord p0 mwfff000fc000000003fqc30c30c30c30c30c30 = mwfff000fc000000003fqc30c30c30c30c30c30 := by decide +kernel
theorem mv1_mw0q82082082082082082 : relWord p1 mw0q82082082082082082 = mw0q41041041041041041 := by decide +kernel
theorem mv1_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p1 mw3ffc0000fc0q8a28a28a28a28a28a2 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv1_mwfff00000003f000q861861861861861861 : relWord p1 mwfff00000003f000q861861861861861861 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv1_mw3f03f00003f00003fq28a28a28a28a28a28a : relWord p1 mw3f03f00003f00003fq28a28a28a28a28a28a = mwfc0fc0fc003fq249249249249249249 := by decide +kernel
theorem mv2_mwfc0q0 : relWord p2 mwfc0q0 = mw3fq0 := by decide +kernel
theorem mv2_mw3ffc003ffffqebaebaebaebaebaeba : relWord p2 mw3ffc003ffffqebaebaebaebaebaeba = mw3fffffffqf3cf3cf3cf3cf3cf3c := by decide +kernel
theorem mv2_mw3f03f00003f00003fq28a28a28a28a28a28a : relWord p2 mw3f03f00003f00003fq28a28a28a28a28a28a = mwfc0fc003f000000fc0q30c30c30c30c30c30c := by decide +kernel
theorem mv3_mw3f000q0 : relWord p3 mw3f000q0 = mw3fq0 := by decide +kernel
theorem mv3_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p3 mw3ffc0000fc0q8a28a28a28a28a28a2 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv3_mwfff00000003ffffqe79e79e79e79e79e79 : relWord p3 mwfff00000003ffffqe79e79e79e79e79e79 = mw3fffffffqf3cf3cf3cf3cf3cf3c := by decide +kernel
theorem mv3_mwfff000fc000000003fqc30c30c30c30c30c30 : relWord p3 mwfff000fc000000003fqc30c30c30c30c30c30 = mwfff000fc0000000fc0qc30c30c30c30c30c30 := by decide +kernel
theorem mv4_mw3ffc003fq924924924924924924 : relWord p4 mw3ffc003fq924924924924924924 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv4_mwfff00000003f000q861861861861861861 : relWord p4 mwfff00000003f000q861861861861861861 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv4_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p4 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv4_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p4 mwfff000fc0000000000qc30c30c30c30c30c30 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv6_mw3ffffq618618618618618618 : relWord p6 mw3ffffq618618618618618618 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv6_mwfc0fc0fc0000q249249249249249249 : relWord p6 mwfc0fc0fc0000q249249249249249249 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv6_mwfff00000003f03fq861861861861861861 : relWord p6 mwfff00000003f03fq861861861861861861 = mw3f03f00003f00003fq28a28a28a28a28a28a := by decide +kernel
theorem mv6_mwfc0fc003f00000003fq30c30c30c30c30c30c : relWord p6 mwfc0fc003f00000003fq30c30c30c30c30c30c = mwfff000fc000000003fqc30c30c30c30c30c30 := by decide +kernel
theorem mv6_mwfff000fc000000003fqc30c30c30c30c30c30 : relWord p6 mwfff000fc000000003fqc30c30c30c30c30c30 = mwfc0fc003f00000003fq30c30c30c30c30c30c := by decide +kernel
theorem mv7_mw3ffc003fq965965965965965965 : relWord p7 mw3ffc003fq965965965965965965 = mw3ffffq659659659659659659 := by decide +kernel
theorem mv7_mwfff00000003f000q861861861861861861 : relWord p7 mwfff00000003f000q861861861861861861 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv7_mw3f03f00003fffffffqfbefbefbefbefbefbe : relWord p7 mw3f03f00003fffffffqfbefbefbefbefbefbe = mw3ffffffffffqfbefbefbefbefbefbe := by decide +kernel
theorem mv8_mwfc0q820820820820820820 : relWord p8 mwfc0q820820820820820820 = mw3fq208208208208208208 := by decide +kernel
theorem mv8_mw3ffc0000fc0qaaaaaaaaaaaaaaaaaa : relWord p8 mw3ffc0000fc0qaaaaaaaaaaaaaaaaaa = mw3ffffqe38e38e38e38e38e38 := by decide +kernel
theorem mv8_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p8 mw3f03f00003f000000q28a28a28a28a28a28a = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv8_mwfc0fc003fffffc0fffqbaebaebaebaebaebae : relWord p8 mwfc0fc003fffffc0fffqbaebaebaebaebaebae = mwffffc0fc0ffffffqe79e79e79e79e79e79 := by decide +kernel
theorem mv9_mw3ffc003fq924924924924924924 : relWord p9 mw3ffc003fq924924924924924924 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv9_mwfc0fc0fc003fq249249249249249249 : relWord p9 mwfc0fc0fc003fq249249249249249249 = mwfff000fc0000fc0000qc30c30c30c30c30c30 := by decide +kernel
theorem mv9_mwfff00000003f000qa69a69a69a69a69a69 : relWord p9 mwfff00000003f000qa69a69a69a69a69a69 = mw3ffffqe38e38e38e38e38e38 := by decide +kernel
theorem mv9_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p9 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv9_mwfff000fc003ffc003fqd34d34d34d34d34d34 : relWord p9 mwfff000fc003ffc003fqd34d34d34d34d34d34 = mwfc0fc0ffffc0fc0000q34d34d34d34d34d34d := by decide +kernel
theorem mv10_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p10 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv10_mwfffffffc0ffffc0qaebaebaebaebaebaeb : relWord p10 mwfffffffc0ffffc0qaebaebaebaebaebaeb = mwffffc0fc0ffffffqe79e79e79e79e79e79 := by decide +kernel
theorem mv10_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p10 mwfff000fc0000000000qc30c30c30c30c30c30 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv11_mwfff00000003f000q861861861861861861 : relWord p11 mwfff00000003f000q861861861861861861 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv11_mwfff000fc0000fc0000qc30c30c30c30c30c30 : relWord p11 mwfff000fc0000fc0000qc30c30c30c30c30c30 = mwffffc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv12_mwfc0000000q820820820820820820 : relWord p12 mwfc0000000q820820820820820820 = mw3fq208208208208208208 := by decide +kernel
theorem mv12_mwfff00000003f000q861861861861861861 : relWord p12 mwfff00000003f000q861861861861861861 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv12_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p12 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv13_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p13 mw3ffc0000fc0q8a28a28a28a28a28a2 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv13_mwffffc0fc0fff000qa69a69a69a69a69a69 : relWord p13 mwffffc0fc0fff000qa69a69a69a69a69a69 = mwfff000fc000003ffffqe38e38e38e38e38e38 := by decide +kernel
theorem mv13_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p13 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv14_mwfc0000q820820820820820820 : relWord p14 mwfc0000q820820820820820820 = mw3fq208208208208208208 := by decide +kernel
theorem mv14_mwfc0ffffc003fqb6db6db6db6db6db6d : relWord p14 mwfc0ffffc003fqb6db6db6db6db6db6d = mw3fffffffqf3cf3cf3cf3cf3cf3c := by decide +kernel
theorem mv14_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p14 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv15_mw3ffc003fq924924924924924924 : relWord p15 mw3ffc003fq924924924924924924 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv15_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p15 mw3f03f00003f000000q28a28a28a28a28a28a = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv16_mw3ffffq618618618618618618 : relWord p16 mw3ffffq618618618618618618 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv16_mwfc0000000000000q0 : relWord p16 mwfc0000000000000q0 = mw3fq0 := by decide +kernel
theorem mv16_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p16 mwfc0fc003f000000000q30c30c30c30c30c30c = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv16_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p16 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv17_mw3f000000000q104104104104104104 : relWord p17 mw3f000000000q104104104104104104 = mw3fq104104104104104104 := by decide +kernel
theorem mv17_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p17 mw3f03f00003f000000q28a28a28a28a28a28a = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv18_mw0q410410410410410410 : relWord p18 mw0q410410410410410410 = mw0q41041041041041041 := by decide +kernel
theorem mv18_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p18 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv18_mwfff00000003ffffq861861861861861861 : relWord p18 mwfff00000003ffffq861861861861861861 = mwfff000fc0fc0fc0000qc30c30c30c30c30c30 := by decide +kernel
theorem mv18_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p18 mwfc0fc003f000000000q30c30c30c30c30c30c = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv19_mw3ffffq618618618618618618 : relWord p19 mw3ffffq618618618618618618 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv19_mwfc0fc0fc0000q249249249249249249 : relWord p19 mwfc0fc0fc0000q249249249249249249 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv19_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p19 mw3f03f00003f000000q28a28a28a28a28a28a = mw3ffffq618618618618618618 := by decide +kernel
theorem mv20_mwfc0000q208208208208208208 : relWord p20 mwfc0000q208208208208208208 = mw3fq208208208208208208 := by decide +kernel
theorem mv20_mwfc0fc0fc003fq249249249249249249 : relWord p20 mwfc0fc0fc003fq249249249249249249 = mwffffffq618618618618618618 := by decide +kernel
theorem mv20_mwffffc0fc0fff000qa69a69a69a69a69a69 : relWord p20 mwffffc0fc0fff000qa69a69a69a69a69a69 = mwfff000fc000003ffffqe38e38e38e38e38e38 := by decide +kernel
theorem mv21_mw3ffffq618618618618618618 : relWord p21 mw3ffffq618618618618618618 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv21_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p21 mw3ffc0000fc0q8a28a28a28a28a28a2 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv21_mwfc0fc0fc0000q249249249249249249 : relWord p21 mwfc0fc0fc0000q249249249249249249 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv21_mw3f03f03ffff000fc0qaaaaaaaaaaaaaaaaaa : relWord p21 mw3f03f03ffff000fc0qaaaaaaaaaaaaaaaaaa = mwfff000fc000003ffffqe38e38e38e38e38e38 := by decide +kernel
theorem mv22_mw3ffc003fq924924924924924924 : relWord p22 mw3ffc003fq924924924924924924 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv22_mwfc0fc0fc0000q249249249249249249 : relWord p22 mwfc0fc0fc0000q249249249249249249 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv22_mwfff00003ffff03fq965965965965965965 : relWord p22 mwfff00003ffff03fq965965965965965965 = mwfff000fc003ffc003fqd34d34d34d34d34d34 := by decide +kernel
theorem mv22_mwfff000fc003ffc003fqd34d34d34d34d34d34 : relWord p22 mwfff000fc003ffc003fqd34d34d34d34d34d34 = mwfffffffc000003f000qc71c71c71c71c71c71 := by decide +kernel
theorem mv23_mw3fffffffqf3cf3cf3cf3cf3cf3c : relWord p23 mw3fffffffqf3cf3cf3cf3cf3cf3c = mwfff000fc0fc0fc0000qe79e79e79e79e79e79 := by decide +kernel
theorem mv23_mwfc0fc0fc0000q249249249249249249 : relWord p23 mwfc0fc0fc0000q249249249249249249 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv23_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p23 mwfc0fc003f000000000q30c30c30c30c30c30c = mw3ffffq618618618618618618 := by decide +kernel
theorem mv24_mw0qc30c30c30c30c30c30 : relWord p24 mw0qc30c30c30c30c30c30 = mw0q249249249249249249 := by decide +kernel
theorem mv24_mwfc0fc0fc0000q249249249249249249 : relWord p24 mwfc0fc0fc0000q249249249249249249 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv24_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p24 mwfff000fc0000000000qc30c30c30c30c30c30 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv25_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p25 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv25_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p25 mwfc0fc003f000000000q30c30c30c30c30c30c = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv28_mw3ffc003fq924924924924924924 : relWord p28 mw3ffc003fq924924924924924924 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv28_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p28 mw3f03f00003f000000q28a28a28a28a28a28a = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv28_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p28 mwfff000fc0000000000qc30c30c30c30c30c30 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv30_mw3ffc003fq924924924924924924 : relWord p30 mw3ffc003fq924924924924924924 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv30_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p30 mw3f03f00003f000000q28a28a28a28a28a28a = mw3ffffq618618618618618618 := by decide +kernel
theorem mv31_mw3ffffq618618618618618618 : relWord p31 mw3ffffq618618618618618618 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv31_mwfff00000003f000q861861861861861861 : relWord p31 mwfff00000003f000q861861861861861861 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv31_mwfff000ffffc0000fc0qcb2cb2cb2cb2cb2cb2 : relWord p31 mwfff000ffffc0000fc0qcb2cb2cb2cb2cb2cb2 = mw3fffffc0fffq9a69a69a69a69a69a6 := by decide +kernel
theorem mv33_mw3fffffc0fffq9a69a69a69a69a69a6 : relWord p33 mw3fffffc0fffq9a69a69a69a69a69a6 = mwfff000fc003ffc003fqd34d34d34d34d34d34 := by decide +kernel
theorem mv33_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p33 mw3f03f00003f000000q28a28a28a28a28a28a = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv33_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p33 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv34_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p34 mw3ffc0000fc0q8a28a28a28a28a28a2 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv34_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p34 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv35_mw3ffc003fq924924924924924924 : relWord p35 mw3ffc003fq924924924924924924 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv35_mwffffc0fc0fc0qaebaebaebaebaebaeb : relWord p35 mwffffc0fc0fc0qaebaebaebaebaebaeb = mwfff000fc0fc0fc0000qe79e79e79e79e79e79 := by decide +kernel
theorem mv35_mw3fffffc0ffffff000qaebaebaebaebaebaeb : relWord p35 mw3fffffc0ffffff000qaebaebaebaebaebaeb = mwffffc0fc0ffffffqe79e79e79e79e79e79 := by decide +kernel
theorem mv36_mw3ffffq618618618618618618 : relWord p36 mw3ffffq618618618618618618 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv36_mwfff00000003f000q861861861861861861 : relWord p36 mwfff00000003f000q861861861861861861 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv36_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p36 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv38_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p38 mw3ffc0000fc0q8a28a28a28a28a28a2 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv38_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p38 mw3f03f00003f000000q28a28a28a28a28a28a = mw3ffffq618618618618618618 := by decide +kernel
theorem mv39_mw3ffffq618618618618618618 : relWord p39 mw3ffffq618618618618618618 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv39_mwfc0fc0fc0000q249249249249249249 : relWord p39 mwfc0fc0fc0000q249249249249249249 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv39_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p39 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv40_mw3ffffq618618618618618618 : relWord p40 mw3ffffq618618618618618618 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv40_mwfff00000003f000q861861861861861861 : relWord p40 mwfff00000003f000q861861861861861861 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv40_mwfff000fc000000003fqc30c30c30c30c30c30 : relWord p40 mwfff000fc000000003fqc30c30c30c30c30c30 = mw3f03ffc003fq924924924924924924 := by decide +kernel
theorem mv42_mwfc0fc0fc0000q249249249249249249 : relWord p42 mwfc0fc0fc0000q249249249249249249 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv42_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p42 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv44_mw3ffffq618618618618618618 : relWord p44 mw3ffffq618618618618618618 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv44_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p44 mw3f03f00003f000000q28a28a28a28a28a28a = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv45_mw3ffffq618618618618618618 : relWord p45 mw3ffffq618618618618618618 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv45_mwfc0fc0fc0000q249249249249249249 : relWord p45 mwfc0fc0fc0000q249249249249249249 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv45_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p45 mwfc0fc003f000000000q30c30c30c30c30c30c = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv46_mw3fffffffqf3cf3cf3cf3cf3cf3c : relWord p46 mw3fffffffqf3cf3cf3cf3cf3cf3c = mwfff000fc0fc0fc0000qe79e79e79e79e79e79 := by decide +kernel
theorem mv46_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p46 mw3f03f00003f000000q28a28a28a28a28a28a = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv47_mw3ffc003fq924924924924924924 : relWord p47 mw3ffc003fq924924924924924924 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv47_mwfc0fc0ffffffq659659659659659659 : relWord p47 mwfc0fc0ffffffq659659659659659659 = mwfff000fc003ffc003fqd34d34d34d34d34d34 := by decide +kernel
theorem mv47_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p47 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3ffffq618618618618618618 := by decide +kernel
end PEqualNP.Outside.Meta617

namespace PEqualNP.Outside.Meta617
set_option maxHeartbeats 2000000
theorem mv0_mwfffq0 : relWord p0 mwfffq0 = mwfffq0 := by decide +kernel
theorem mv0_mw3ffc003fq924924924924924924 : relWord p0 mw3ffc003fq924924924924924924 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv0_mw3ffffffffffqfbefbefbefbefbefbe : relWord p0 mw3ffffffffffqfbefbefbefbefbefbe = mw3ffffffffffqfbefbefbefbefbefbe := by decide +kernel
theorem mv0_mwffffc0fc0fff000qa69a69a69a69a69a69 : relWord p0 mwffffc0fc0fff000qa69a69a69a69a69a69 = mwffffc0fc0fff000qa69a69a69a69a69a69 := by decide +kernel
theorem mv0_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p0 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv0_mwfff000fc0000000fffqc30c30c30c30c30c30 : relWord p0 mwfff000fc0000000fffqc30c30c30c30c30c30 = mwfff000fc0000000fffqc30c30c30c30c30c30 := by decide +kernel
theorem mv1_mw3fq0 : relWord p1 mw3fq0 = mw3fq0 := by decide +kernel
theorem mv1_mw3ffc0000fffq8a28a28a28a28a28a2 : relWord p1 mw3ffc0000fffq8a28a28a28a28a28a2 = mwfff00000003f03fq861861861861861861 := by decide +kernel
theorem mv1_mwfff00003ffff03fq965965965965965965 : relWord p1 mwfff00003ffff03fq965965965965965965 = mw3fffffc0fffq9a69a69a69a69a69a6 := by decide +kernel
theorem mv1_mw3f03f03ffff000fc0qaaaaaaaaaaaaaaaaaa : relWord p1 mw3f03f03ffff000fc0qaaaaaaaaaaaaaaaaaa = mwffffc0fc0fff000qa69a69a69a69a69a69 := by decide +kernel
theorem mv2_mw3ffffq618618618618618618 : relWord p2 mw3ffffq618618618618618618 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv2_mwfc0fc0fc0000q249249249249249249 : relWord p2 mwfc0fc0fc0000q249249249249249249 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv2_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p2 mwfc0fc003f000000000q30c30c30c30c30c30c = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv3_mw3f000q208208208208208208 : relWord p3 mw3f000q208208208208208208 = mw3fq208208208208208208 := by decide +kernel
theorem mv3_mwfc0fc0fc0000q249249249249249249 : relWord p3 mwfc0fc0fc0000q249249249249249249 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv3_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p3 mw3f03f00003f000000q28a28a28a28a28a28a = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv4_mw0q104104104104104104 : relWord p4 mw0q104104104104104104 = mw0q41041041041041041 := by decide +kernel
theorem mv4_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p4 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv4_mwfff03ffc003ffc0q8e38e38e38e38e38e3 : relWord p4 mwfff03ffc003ffc0q8e38e38e38e38e38e3 = mw3fffffc0fffq9a69a69a69a69a69a6 := by decide +kernel
theorem mv4_mwfc0fc003f00000003fq30c30c30c30c30c30c : relWord p4 mwfc0fc003f00000003fq30c30c30c30c30c30c = mwfc0fc0fff000q249249249249249249 := by decide +kernel
theorem mv4_mwfff000fc003ffc003fqd34d34d34d34d34d34 : relWord p4 mwfff000fc003ffc003fqd34d34d34d34d34d34 = mwfffffffc000003f000qc71c71c71c71c71c71 := by decide +kernel
theorem mv6_mw3ffc003fq924924924924924924 : relWord p6 mw3ffc003fq924924924924924924 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv6_mwfc0fc0ffffffq659659659659659659 : relWord p6 mwfc0fc0ffffffq659659659659659659 = mw3fffffc0fffq9a69a69a69a69a69a6 := by decide +kernel
theorem mv6_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p6 mw3f03f00003f000000q28a28a28a28a28a28a = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv6_mwfc0fc003f000000fffq30c30c30c30c30c30c : relWord p6 mwfc0fc003f000000fffq30c30c30c30c30c30c = mwfff000fc0000fc003fqc30c30c30c30c30c30 := by decide +kernel
theorem mv7_mw3fq0 : relWord p7 mw3fq0 = mw3fq0 := by decide +kernel
theorem mv7_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p7 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv7_mwffffc0ffffff03fqb6db6db6db6db6db6d : relWord p7 mwffffc0ffffff03fqb6db6db6db6db6db6d = mwffffc0fc0ffffffqe79e79e79e79e79e79 := by decide +kernel
theorem mv7_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p7 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv8_mw3ffffq618618618618618618 : relWord p8 mw3ffffq618618618618618618 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv8_mw3ffc0000fffq8a28a28a28a28a28a2 : relWord p8 mw3ffc0000fffq8a28a28a28a28a28a2 = mwffffffq618618618618618618 := by decide +kernel
theorem mv8_mw3f03f00003f00003fq28a28a28a28a28a28a : relWord p8 mw3f03f00003f00003fq28a28a28a28a28a28a = mwfff000fc0000fc0000qc30c30c30c30c30c30 := by decide +kernel
theorem mv8_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p8 mwfff000fc0000000000qc30c30c30c30c30c30 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv9_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p9 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv9_mwfc0fc0fc0fffq249249249249249249 : relWord p9 mwfc0fc0fc0fffq249249249249249249 = mwfff000fc003ffc0000qc30c30c30c30c30c30 := by decide +kernel
theorem mv9_mwfff00000003f03fq861861861861861861 : relWord p9 mwfff00000003f03fq861861861861861861 = mwffffffq618618618618618618 := by decide +kernel
theorem mv9_mwfc0fc0ffffc0fc0000q34d34d34d34d34d34d : relWord p9 mwfc0fc0ffffc0fc0000q34d34d34d34d34d34d = mwfffffffc000003f000qc71c71c71c71c71c71 := by decide +kernel
theorem mv9_mwfff000ffffc0000fc0qcb2cb2cb2cb2cb2cb2 : relWord p9 mwfff000ffffc0000fc0qcb2cb2cb2cb2cb2cb2 = mwffffff03f03f000000q38e38e38e38e38e38e := by decide +kernel
theorem mv10_mw3ffc0000fc0q8e38e38e38e38e38e3 : relWord p10 mw3ffc0000fc0q8e38e38e38e38e38e3 = mw3ffffq659659659659659659 := by decide +kernel
theorem mv10_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p10 mw3f03f00003f000000q28a28a28a28a28a28a = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv11_mw3ffffq618618618618618618 : relWord p11 mw3ffffq618618618618618618 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv11_mwfff00003ffff03fq965965965965965965 : relWord p11 mwfff00003ffff03fq965965965965965965 = mw3f03f00003f03ffffq69a69a69a69a69a69a := by decide +kernel
theorem mv12_mw3ffffq618618618618618618 : relWord p12 mw3ffffq618618618618618618 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv12_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p12 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv12_mwfff00000003f03fq861861861861861861 : relWord p12 mwfff00000003f03fq861861861861861861 = mwfc0fc003ffc0000000q30c30c30c30c30c30c := by decide +kernel
theorem mv12_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p12 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv13_mwfc0fc0fc0000q249249249249249249 : relWord p13 mwfc0fc0fc0000q249249249249249249 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv13_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p13 mw3f03f00003f000000q28a28a28a28a28a28a = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv13_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p13 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv14_mw3ffc003fq924924924924924924 : relWord p14 mw3ffc003fq924924924924924924 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv14_mwfff00000003f000q861861861861861861 : relWord p14 mwfff00000003f000q861861861861861861 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv15_mw3ffffq618618618618618618 : relWord p15 mw3ffffq618618618618618618 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv15_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p15 mw3ffc0000fc0q8a28a28a28a28a28a2 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv15_mw3f03f00003ffc003fqbaebaebaebaebaebae : relWord p15 mw3f03f00003ffc003fqbaebaebaebaebaebae = mw3fffffffqf3cf3cf3cf3cf3cf3c := by decide +kernel
theorem mv16_mw3ffc003fq924924924924924924 : relWord p16 mw3ffc003fq924924924924924924 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv16_mwfff00000003f000q861861861861861861 : relWord p16 mwfff00000003f000q861861861861861861 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv16_mwfc0fc003f00000003fq30c30c30c30c30c30c : relWord p16 mwfc0fc003f00000003fq30c30c30c30c30c30c = mw3f03ffc003fq924924924924924924 := by decide +kernel
theorem mv17_mw3ffffq618618618618618618 : relWord p17 mw3ffffq618618618618618618 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv17_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p17 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv17_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p17 mwfc0fc003f000000000q30c30c30c30c30c30c = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv18_mw3ffffq618618618618618618 : relWord p18 mw3ffffq618618618618618618 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv18_mwfc0fc0fc0000q249249249249249249 : relWord p18 mwfc0fc0fc0000q249249249249249249 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv18_mwfff03ffc003ffc0q8e38e38e38e38e38e3 : relWord p18 mwfff03ffc003ffc0q8e38e38e38e38e38e3 = mwfff000fc003ffc003fqd34d34d34d34d34d34 := by decide +kernel
theorem mv18_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p18 mwfff000fc0000000000qc30c30c30c30c30c30 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv19_mw3ffc003fq924924924924924924 : relWord p19 mw3ffc003fq924924924924924924 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv19_mw3f000000000000q208208208208208208 : relWord p19 mw3f000000000000q208208208208208208 = mw3fq208208208208208208 := by decide +kernel
theorem mv19_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p19 mwfc0fc003f000000000q30c30c30c30c30c30c = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv20_mw3ffc003fq924924924924924924 : relWord p20 mw3ffc003fq924924924924924924 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv20_mwfff00000003f000q861861861861861861 : relWord p20 mwfff00000003f000q861861861861861861 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv20_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p20 mw3f03f00003f000000q28a28a28a28a28a28a = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv21_mw3f000000q0 : relWord p21 mw3f000000q0 = mw3fq0 := by decide +kernel
theorem mv21_mw3ffc0000fffq8a28a28a28a28a28a2 : relWord p21 mw3ffc0000fffq8a28a28a28a28a28a2 = mwfff000fc0000fc0000qc30c30c30c30c30c30 := by decide +kernel
theorem mv21_mwfff00000003f000q861861861861861861 : relWord p21 mwfff00000003f000q861861861861861861 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv21_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p21 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv22_mw3fffffffqf3cf3cf3cf3cf3cf3c : relWord p22 mw3fffffffqf3cf3cf3cf3cf3cf3c = mwfff000fc0fc0fc0000qe79e79e79e79e79e79 := by decide +kernel
theorem mv22_mwfc0fc0fc003fq249249249249249249 : relWord p22 mwfc0fc0fc003fq249249249249249249 = mwfc0fc0fff000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv22_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p22 mw3f03f00003f000000q28a28a28a28a28a28a = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv23_mw3ffffq618618618618618618 : relWord p23 mw3ffffq618618618618618618 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv23_mw3f000000000q0 : relWord p23 mw3f000000000q0 = mw3fq0 := by decide +kernel
theorem mv23_mwfff00000003f000q861861861861861861 : relWord p23 mwfff00000003f000q861861861861861861 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv23_mwfc0fc003f03ffc003fqb2cb2cb2cb2cb2cb2c : relWord p23 mwfc0fc003f03ffc003fqb2cb2cb2cb2cb2cb2c = mwfff000fc000003ffffqe38e38e38e38e38e38 := by decide +kernel
theorem mv24_mw3ffffq618618618618618618 : relWord p24 mw3ffffq618618618618618618 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv24_mwfff00000003f000q861861861861861861 : relWord p24 mwfff00000003f000q861861861861861861 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv24_mwffffff03f03f000000q38e38e38e38e38e38e : relWord p24 mwffffff03f03f000000q38e38e38e38e38e38e = mw3fffffc0fffq9a69a69a69a69a69a6 := by decide +kernel
theorem mv25_mwfc0fc0fc0000q249249249249249249 : relWord p25 mwfc0fc0fc0000q249249249249249249 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv25_mwfc0fc0ffffc0fc0000q34d34d34d34d34d34d : relWord p25 mwfc0fc0ffffc0fc0000q34d34d34d34d34d34d = mw3fffffc0fffq9a69a69a69a69a69a6 := by decide +kernel
theorem mv28_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p28 mw3ffc0000fc0q8a28a28a28a28a28a2 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv28_mw3f03ffc0ffffc0000q2cb2cb2cb2cb2cb2cb : relWord p28 mw3f03ffc0ffffc0000q2cb2cb2cb2cb2cb2cb = mw3fffffc0fffq9a69a69a69a69a69a6 := by decide +kernel
theorem mv28_mwfff000fc000000003fqc30c30c30c30c30c30 : relWord p28 mwfff000fc000000003fqc30c30c30c30c30c30 = mwfc0fc0fff000q249249249249249249 := by decide +kernel
theorem mv30_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p30 mw3ffc0000fc0q8a28a28a28a28a28a2 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv30_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p30 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv31_mw3ffc003fq924924924924924924 : relWord p31 mw3ffc003fq924924924924924924 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv31_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p31 mw3f03f00003f000000q28a28a28a28a28a28a = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv33_mw3ffffq618618618618618618 : relWord p33 mw3ffffq618618618618618618 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv33_mwfc0fc0fc0000q249249249249249249 : relWord p33 mwfc0fc0fc0000q249249249249249249 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv33_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p33 mwfc0fc003f000000000q30c30c30c30c30c30c = mw3ffffq618618618618618618 := by decide +kernel
theorem mv33_mwfff000fc003ffc003fqd34d34d34d34d34d34 : relWord p33 mwfff000fc003ffc003fqd34d34d34d34d34d34 = mwfff000ffffc0000fc0qcb2cb2cb2cb2cb2cb2 := by decide +kernel
theorem mv34_mwfc0fc0fc0000q249249249249249249 : relWord p34 mwfc0fc0fc0000q249249249249249249 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv34_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p34 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv35_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p35 mw3ffc0000fc0q8a28a28a28a28a28a2 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv35_mwfff00000003f000q861861861861861861 : relWord p35 mwfff00000003f000q861861861861861861 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv35_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p35 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv36_mw3ffc003fq924924924924924924 : relWord p36 mw3ffc003fq924924924924924924 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv36_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p36 mw3f03f00003f000000q28a28a28a28a28a28a = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv36_mwffffc0fff000000000qf3cf3cf3cf3cf3cf3c : relWord p36 mwffffc0fff000000000qf3cf3cf3cf3cf3cf3c = mw3fffffffqf3cf3cf3cf3cf3cf3c := by decide +kernel
theorem mv38_mwfc0fc0fc0000q249249249249249249 : relWord p38 mwfc0fc0fc0000q249249249249249249 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv38_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p38 mwfc0fc003f000000000q30c30c30c30c30c30c = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv39_mw3ffc003fq924924924924924924 : relWord p39 mw3ffc003fq924924924924924924 = mwfff00000003f000q861861861861861861 := by decide +kernel
theorem mv39_mwfff00000003f000q861861861861861861 : relWord p39 mwfff00000003f000q861861861861861861 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv39_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p39 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3ffc003fq924924924924924924 := by decide +kernel
theorem mv40_mw3ffc003fq924924924924924924 : relWord p40 mw3ffc003fq924924924924924924 = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv40_mw3f03f00003f000000q28a28a28a28a28a28a : relWord p40 mw3f03f00003f000000q28a28a28a28a28a28a = mw3ffffq618618618618618618 := by decide +kernel
theorem mv42_mw3ffffq618618618618618618 : relWord p42 mw3ffffq618618618618618618 = mwfff000fc0000000000qc30c30c30c30c30c30 := by decide +kernel
theorem mv42_mwfff00000003f000q861861861861861861 : relWord p42 mwfff00000003f000q861861861861861861 = mwfc0fc0fc0000q249249249249249249 := by decide +kernel
theorem mv42_mwfff000fc0000000000qc71c71c71c71c71c71 : relWord p42 mwfff000fc0000000000qc71c71c71c71c71c71 = mw3ffffq659659659659659659 := by decide +kernel
theorem mv44_mw3ffc0000fffq8a28a28a28a28a28a2 : relWord p44 mw3ffc0000fffq8a28a28a28a28a28a2 = mwffffc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv44_mwfc0fc003f000000000q30c30c30c30c30c30c : relWord p44 mwfc0fc003f000000000q30c30c30c30c30c30c = mw3ffc0000fc0q8a28a28a28a28a28a2 := by decide +kernel
theorem mv45_mw3ffc003fq924924924924924924 : relWord p45 mw3ffc003fq924924924924924924 = mw3f03f00003f000000q28a28a28a28a28a28a := by decide +kernel
theorem mv45_mwfff00000003f000q861861861861861861 : relWord p45 mwfff00000003f000q861861861861861861 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv45_mwfff000fc0000000000qc30c30c30c30c30c30 : relWord p45 mwfff000fc0000000000qc30c30c30c30c30c30 = mw3ffffq618618618618618618 := by decide +kernel
theorem mv46_mw3ffc0000fc0q8a28a28a28a28a28a2 : relWord p46 mw3ffc0000fc0q8a28a28a28a28a28a2 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
theorem mv46_mw3f03f00003f03ffffq69a69a69a69a69a69a : relWord p46 mw3f03f00003f03ffffq69a69a69a69a69a69a = mwfff000fc003ffc003fqd34d34d34d34d34d34 := by decide +kernel
theorem mv47_mw3fffffffqf3cf3cf3cf3cf3cf3c : relWord p47 mw3fffffffqf3cf3cf3cf3cf3cf3c = mwfff000fc0fc0fc0000qe79e79e79e79e79e79 := by decide +kernel
theorem mv47_mwfff00000003f000q861861861861861861 : relWord p47 mwfff00000003f000q861861861861861861 = mwfc0fc003f000000000q30c30c30c30c30c30c := by decide +kernel
end PEqualNP.Outside.Meta617

/- Induction over the 45 excluded states, ending with the posted statement -/

namespace PEqualNP.Outside.Meta617
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
theorem excluded0 : ¬ Viable 7 node0 := by
  refine trace_close (r:=6) (xs:=node0) tab0 cert0 ?_ uniq0
  intro v hv
  simp [tab0] at hv
theorem excluded1 : ¬ Viable 7 node1 := by
  refine trace_close (r:=6) (xs:=node1) tab1 cert1 ?_ uniq1
  intro v hv
  simp [tab1] at hv
private theorem im2q0 : (child2q0.toFinset.image (relWord p11)) = node0.toFinset := by
  simp only [child2q0,node0, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv11_mwfff00003ffff03fq965965965965965965,mv11_mw3ffffq618618618618618618,mv11_mw3ffc0000fc0q8a28a28a28a28a28a2,mv11_mwfc0fc0fc0000q249249249249249249,mv11_mwfff00000003f000q861861861861861861,mv11_mw3f03f00003f000000q28a28a28a28a28a28a,mv11_mwfc0fc003f000000000q30c30c30c30c30c30c,mv11_mwfff000fc0000fc0000qc30c30c30c30c30c30]
  decide +kernel
private theorem im2q1 : (child2q1.toFinset.image (relWord p9)) = node1.toFinset := by
  simp only [child2q1,node1, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv9_mwfc0fc0ffffc0fc0000q34d34d34d34d34d34d,mv9_mw3ffffq618618618618618618,mv9_mw3ffc003fq924924924924924924,mv9_mw3ffc0000fc0q8a28a28a28a28a28a2,mv9_mwfff00000003f000q861861861861861861,mv9_mw3f03f00003f000000q28a28a28a28a28a28a,mv9_mwfc0fc003f000000000q30c30c30c30c30c30c,mv9_mwfff000fc0000fc0000qc30c30c30c30c30c30]
  decide +kernel
theorem excluded2 : ¬ Viable 8 node2 := by
  refine trace_close (r:=7) (xs:=node2) tab2 cert2 ?_ uniq2
  intro v hv
  simp only [tab2,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl
  · exact not_viable_transport p11 sur11 im2q0 excluded0
  · exact not_viable_transport p9 sur9 im2q1 excluded1
theorem excluded3 : ¬ Viable 7 node3 := by
  refine trace_close (r:=6) (xs:=node3) tab3 cert3 ?_ uniq3
  intro v hv
  simp [tab3] at hv
theorem excluded4 : ¬ Viable 7 node4 := by
  refine trace_close (r:=6) (xs:=node4) tab4 cert4 ?_ uniq4
  intro v hv
  simp [tab4] at hv
theorem excluded5 : ¬ Viable 7 node5 := by
  refine trace_close (r:=6) (xs:=node5) tab5 cert5 ?_ uniq5
  intro v hv
  simp [tab5] at hv
theorem excluded6 : ¬ Viable 7 node6 := by
  refine trace_close (r:=6) (xs:=node6) tab6 cert6 ?_ uniq6
  intro v hv
  simp [tab6] at hv
theorem excluded7 : ¬ Viable 7 node7 := by
  refine trace_close (r:=6) (xs:=node7) tab7 cert7 ?_ uniq7
  intro v hv
  simp [tab7] at hv
private theorem im8q0 : (child8q0.toFinset.image (relWord p1)) = node3.toFinset := by
  simp only [child8q0,node3, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1_mw3ffc0000fffq8a28a28a28a28a28a2,mv1_mw3ffffq618618618618618618,mv1_mw3ffc003fq924924924924924924,mv1_mwfc0fc0fc0000q249249249249249249,mv1_mwfff00000003f000q861861861861861861,mv1_mw3f03f00003f00003fq28a28a28a28a28a28a,mv1_mwfc0fc003f000000000q30c30c30c30c30c30c,mv1_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im8q1 : (child8q1.toFinset.image (relWord p4)) = node4.toFinset := by
  simp only [child8q1,node4, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv4_mwfc0fc0fc003fq249249249249249249,mv4_mw3ffffq618618618618618618,mv4_mw3ffc003fq924924924924924924,mv4_mw3ffc0000fc0q8a28a28a28a28a28a2,mv4_mwfff00000003f000q861861861861861861,mv4_mw3f03f00003f00003fq28a28a28a28a28a28a,mv4_mwfc0fc003f000000000q30c30c30c30c30c30c,mv4_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im8q2 : (child8q2.toFinset.image (relWord p12)) = node5.toFinset := by
  simp only [child8q2,node5, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv12_mwfff00000003f03fq861861861861861861,mv12_mw3ffffq618618618618618618,mv12_mw3ffc003fq924924924924924924,mv12_mw3ffc0000fc0q8a28a28a28a28a28a2,mv12_mwfc0fc0fc0000q249249249249249249,mv12_mw3f03f00003f00003fq28a28a28a28a28a28a,mv12_mwfc0fc003f000000000q30c30c30c30c30c30c,mv12_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im8q3 : (child8q3.toFinset.image (relWord p0)) = node6.toFinset := by
  simp only [child8q3,node6, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mwfc0fc003f00000003fq30c30c30c30c30c30c,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f00003fq28a28a28a28a28a28a,mv0_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im8q4 : (child8q4.toFinset.image (relWord p2)) = node7.toFinset := by
  simp only [child8q4,node7, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2_mwfff000fc000000003fqc30c30c30c30c30c30,mv2_mw3ffffq618618618618618618,mv2_mw3ffc003fq924924924924924924,mv2_mw3ffc0000fc0q8a28a28a28a28a28a2,mv2_mwfc0fc0fc0000q249249249249249249,mv2_mwfff00000003f000q861861861861861861,mv2_mw3f03f00003f00003fq28a28a28a28a28a28a,mv2_mwfc0fc003f000000000q30c30c30c30c30c30c]
  decide +kernel
theorem excluded8 : ¬ Viable 8 node8 := by
  refine trace_close (r:=7) (xs:=node8) tab8 cert8 ?_ uniq8
  intro v hv
  simp only [tab8,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact not_viable_transport p1 sur1 im8q0 excluded3
  · exact not_viable_transport p4 sur4 im8q1 excluded4
  · exact not_viable_transport p12 sur12 im8q2 excluded5
  · exact not_viable_transport p0 sur0 im8q3 excluded6
  · exact not_viable_transport p2 sur2 im8q4 excluded7
theorem excluded9 : ¬ Viable 8 node9 := by
  refine trace_close (r:=7) (xs:=node9) tab9 cert9 ?_ uniq9
  intro v hv
  simp [tab9] at hv
theorem excluded10 : ¬ Viable 7 node10 := by
  refine trace_close (r:=6) (xs:=node10) tab10 cert10 ?_ uniq10
  intro v hv
  simp [tab10] at hv
private theorem im11q0 : (child11q0.toFinset.image (relWord p28)) = node10.toFinset := by
  simp only [child11q0,node10, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv28_mwfc0fc003f00003ffffq71c71c71c71c71c71c,mv28_mw3ffc003fq924924924924924924,mv28_mw3ffc0000fc0q8a28a28a28a28a28a2,mv28_mwfc0fc0fc0000q249249249249249249,mv28_mwfff00000003f000q861861861861861861,mv28_mw3f03f00003f000000q28a28a28a28a28a28a,mv28_mwfc0fc003f000000000q30c30c30c30c30c30c,mv28_mwfff000fc000000003fqc30c30c30c30c30c30]
  decide +kernel
theorem excluded11 : ¬ Viable 8 node11 := by
  refine trace_close (r:=7) (xs:=node11) tab11 cert11 ?_ uniq11
  intro v hv
  simp only [tab11,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl
  · exact not_viable_transport p28 sur28 im11q0 excluded10
theorem excluded12 : ¬ Viable 7 node12 := by
  refine trace_close (r:=6) (xs:=node12) tab12 cert12 ?_ uniq12
  intro v hv
  simp [tab12] at hv
private theorem im13q0 : (child13q0.toFinset.image (relWord p7)) = node6.toFinset := by
  simp only [child13q0,node6, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv7_mw3ffc0000fffq8a28a28a28a28a28a2,mv7_mw3ffffq618618618618618618,mv7_mw3ffc003fq924924924924924924,mv7_mwfc0fc0fc0000q249249249249249249,mv7_mwfff00000003f000q861861861861861861,mv7_mw3f03f00003f000000q28a28a28a28a28a28a,mv7_mwfc0fc003f000000000q30c30c30c30c30c30c,mv7_mwfff000fc000000003fqc30c30c30c30c30c30]
  decide +kernel
private theorem im13q1 : (child13q1.toFinset.image (relWord p3)) = node7.toFinset := by
  simp only [child13q1,node7, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv3_mwfc0fc0fc003fq249249249249249249,mv3_mw3ffffq618618618618618618,mv3_mw3ffc003fq924924924924924924,mv3_mw3ffc0000fc0q8a28a28a28a28a28a2,mv3_mwfff00000003f000q861861861861861861,mv3_mw3f03f00003f000000q28a28a28a28a28a28a,mv3_mwfc0fc003f000000000q30c30c30c30c30c30c,mv3_mwfff000fc000000003fqc30c30c30c30c30c30]
  decide +kernel
private theorem im13q2 : (child13q2.toFinset.image (relWord p6)) = node6.toFinset := by
  simp only [child13q2,node6, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv6_mwfff00000003f03fq861861861861861861,mv6_mw3ffffq618618618618618618,mv6_mw3ffc003fq924924924924924924,mv6_mw3ffc0000fc0q8a28a28a28a28a28a2,mv6_mwfc0fc0fc0000q249249249249249249,mv6_mw3f03f00003f000000q28a28a28a28a28a28a,mv6_mwfc0fc003f000000000q30c30c30c30c30c30c,mv6_mwfff000fc000000003fqc30c30c30c30c30c30]
  decide +kernel
private theorem im13q3 : (child13q3.toFinset.image (relWord p2)) = node7.toFinset := by
  simp only [child13q3,node7, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2_mw3f03f00003f00003fq28a28a28a28a28a28a,mv2_mw3ffffq618618618618618618,mv2_mw3ffc003fq924924924924924924,mv2_mw3ffc0000fc0q8a28a28a28a28a28a2,mv2_mwfc0fc0fc0000q249249249249249249,mv2_mwfff00000003f000q861861861861861861,mv2_mwfc0fc003f000000000q30c30c30c30c30c30c,mv2_mwfff000fc000000003fqc30c30c30c30c30c30]
  decide +kernel
private theorem im13q4 : (child13q4.toFinset.image (relWord p0)) = node12.toFinset := by
  simp only [child13q4,node12, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mwfc0fc003f00000003fq30c30c30c30c30c30c,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfff000fc000000003fqc30c30c30c30c30c30]
  decide +kernel
theorem excluded13 : ¬ Viable 8 node13 := by
  refine trace_close (r:=7) (xs:=node13) tab13 cert13 ?_ uniq13
  intro v hv
  simp only [tab13,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact not_viable_transport p7 sur7 im13q0 excluded6
  · exact not_viable_transport p3 sur3 im13q1 excluded7
  · exact not_viable_transport p6 sur6 im13q2 excluded6
  · exact not_viable_transport p2 sur2 im13q3 excluded7
  · exact not_viable_transport p0 sur0 im13q4 excluded12
theorem excluded14 : ¬ Viable 8 node14 := by
  refine trace_close (r:=7) (xs:=node14) tab14 cert14 ?_ uniq14
  intro v hv
  simp [tab14] at hv
private theorem im15q0 : (child15q0.toFinset.image (relWord p44)) = node0.toFinset := by
  simp only [child15q0,node0, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv44_mw3ffc0000fffq8a28a28a28a28a28a2,mv44_mw3ffffq618618618618618618,mv44_mwfc0fc0fc0000q249249249249249249,mv44_mwfff00000003f000q861861861861861861,mv44_mw3f03f00003f000000q28a28a28a28a28a28a,mv44_mwfc0fc003f000000000q30c30c30c30c30c30c,mv44_mwfff000fc0000000000qc30c30c30c30c30c30,mv44_mwfff000fc003ffc003fqd34d34d34d34d34d34]
  decide +kernel
private theorem im15q1 : (child15q1.toFinset.image (relWord p22)) = node1.toFinset := by
  simp only [child15q1,node1, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv22_mwfc0fc0fc003fq249249249249249249,mv22_mw3ffffq618618618618618618,mv22_mw3ffc0000fc0q8a28a28a28a28a28a2,mv22_mwfff00000003f000q861861861861861861,mv22_mw3f03f00003f000000q28a28a28a28a28a28a,mv22_mwfc0fc003f000000000q30c30c30c30c30c30c,mv22_mwfff000fc0000000000qc30c30c30c30c30c30,mv22_mwfff000fc003ffc003fqd34d34d34d34d34d34]
  decide +kernel
private theorem im15q2 : (child15q2.toFinset.image (relWord p45)) = node0.toFinset := by
  simp only [child15q2,node0, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv45_mwfff00000003f03fq861861861861861861,mv45_mw3ffffq618618618618618618,mv45_mw3ffc0000fc0q8a28a28a28a28a28a2,mv45_mwfc0fc0fc0000q249249249249249249,mv45_mw3f03f00003f000000q28a28a28a28a28a28a,mv45_mwfc0fc003f000000000q30c30c30c30c30c30c,mv45_mwfff000fc0000000000qc30c30c30c30c30c30,mv45_mwfff000fc003ffc003fqd34d34d34d34d34d34]
  decide +kernel
private theorem im15q3 : (child15q3.toFinset.image (relWord p23)) = node1.toFinset := by
  simp only [child15q3,node1, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv23_mw3f03f00003f00003fq28a28a28a28a28a28a,mv23_mw3ffffq618618618618618618,mv23_mw3ffc0000fc0q8a28a28a28a28a28a2,mv23_mwfc0fc0fc0000q249249249249249249,mv23_mwfff00000003f000q861861861861861861,mv23_mwfc0fc003f000000000q30c30c30c30c30c30c,mv23_mwfff000fc0000000000qc30c30c30c30c30c30,mv23_mwfff000fc003ffc003fqd34d34d34d34d34d34]
  decide +kernel
private theorem im15q4 : (child15q4.toFinset.image (relWord p4)) = node10.toFinset := by
  simp only [child15q4,node10, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv4_mwfc0fc003f00000003fq30c30c30c30c30c30c,mv4_mw3ffffq618618618618618618,mv4_mw3ffc0000fc0q8a28a28a28a28a28a2,mv4_mwfc0fc0fc0000q249249249249249249,mv4_mwfff00000003f000q861861861861861861,mv4_mw3f03f00003f000000q28a28a28a28a28a28a,mv4_mwfff000fc0000000000qc30c30c30c30c30c30,mv4_mwfff000fc003ffc003fqd34d34d34d34d34d34]
  decide +kernel
theorem excluded15 : ¬ Viable 8 node15 := by
  refine trace_close (r:=7) (xs:=node15) tab15 cert15 ?_ uniq15
  intro v hv
  simp only [tab15,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact not_viable_transport p44 sur44 im15q0 excluded0
  · exact not_viable_transport p22 sur22 im15q1 excluded1
  · exact not_viable_transport p45 sur45 im15q2 excluded0
  · exact not_viable_transport p23 sur23 im15q3 excluded1
  · exact not_viable_transport p4 sur4 im15q4 excluded10
private theorem im16q0 : (child16q0.toFinset.image (relWord p21)) = node2.toFinset := by
  simp only [child16q0,node2, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv21_mw3ffc0000fffq8a28a28a28a28a28a2,mv21_mw3ffffq618618618618618618,mv21_mw3ffc003fq924924924924924924,mv21_mwfc0fc0fc0000q249249249249249249,mv21_mwfff00000003f000q861861861861861861,mv21_mw3f03f00003f000000q28a28a28a28a28a28a,mv21_mwfc0fc003f000000000q30c30c30c30c30c30c,mv21_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im16q1 : (child16q1.toFinset.image (relWord p7)) = node8.toFinset := by
  simp only [child16q1,node8, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv7_mw3ffc0000fffq8a28a28a28a28a28a2,mv7_mw3fq0,mv7_mw3ffffq618618618618618618,mv7_mw3ffc003fq924924924924924924,mv7_mwfc0fc0fc0000q249249249249249249,mv7_mwfff00000003f000q861861861861861861,mv7_mw3f03f00003f000000q28a28a28a28a28a28a,mv7_mwfc0fc003f000000000q30c30c30c30c30c30c,mv7_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im16q2 : (child16q2.toFinset.image (relWord p8)) = node9.toFinset := by
  simp only [child16q2,node9, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv8_mw3ffc0000fffq8a28a28a28a28a28a2,mv8_mw3ffffq618618618618618618,mv8_mw3ffc003fq924924924924924924,mv8_mw3ffc0000fc0q8a28a28a28a28a28a2,mv8_mwfc0fc0fc0000q249249249249249249,mv8_mwfff00000003f000q861861861861861861,mv8_mw3f03f00003f000000q28a28a28a28a28a28a,mv8_mwfc0fc003f000000000q30c30c30c30c30c30c,mv8_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im16q3 : (child16q3.toFinset.image (relWord p9)) = node2.toFinset := by
  simp only [child16q3,node2, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv9_mwfc0fc0fc003fq249249249249249249,mv9_mw3ffffq618618618618618618,mv9_mw3ffc003fq924924924924924924,mv9_mw3ffc0000fc0q8a28a28a28a28a28a2,mv9_mwfff00000003f000q861861861861861861,mv9_mw3f03f00003f000000q28a28a28a28a28a28a,mv9_mwfc0fc003f000000000q30c30c30c30c30c30c,mv9_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im16q4 : (child16q4.toFinset.image (relWord p1)) = node8.toFinset := by
  simp only [child16q4,node8, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1_mwfc0fc0fc003fq249249249249249249,mv1_mw3fq0,mv1_mw3ffffq618618618618618618,mv1_mw3ffc003fq924924924924924924,mv1_mw3ffc0000fc0q8a28a28a28a28a28a2,mv1_mwfff00000003f000q861861861861861861,mv1_mw3f03f00003f000000q28a28a28a28a28a28a,mv1_mwfc0fc003f000000000q30c30c30c30c30c30c,mv1_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im16q5 : (child16q5.toFinset.image (relWord p20)) = node9.toFinset := by
  simp only [child16q5,node9, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv20_mwfc0fc0fc003fq249249249249249249,mv20_mw3ffffq618618618618618618,mv20_mw3ffc003fq924924924924924924,mv20_mw3ffc0000fc0q8a28a28a28a28a28a2,mv20_mwfc0fc0fc0000q249249249249249249,mv20_mwfff00000003f000q861861861861861861,mv20_mw3f03f00003f000000q28a28a28a28a28a28a,mv20_mwfc0fc003f000000000q30c30c30c30c30c30c,mv20_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im16q6 : (child16q6.toFinset.image (relWord p20)) = node2.toFinset := by
  simp only [child16q6,node2, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv20_mwfff00000003f03fq861861861861861861,mv20_mw3ffffq618618618618618618,mv20_mw3ffc003fq924924924924924924,mv20_mw3ffc0000fc0q8a28a28a28a28a28a2,mv20_mwfc0fc0fc0000q249249249249249249,mv20_mw3f03f00003f000000q28a28a28a28a28a28a,mv20_mwfc0fc003f000000000q30c30c30c30c30c30c,mv20_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im16q7 : (child16q7.toFinset.image (relWord p6)) = node8.toFinset := by
  simp only [child16q7,node8, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv6_mwfff00000003f03fq861861861861861861,mv6_mw3fq0,mv6_mw3ffffq618618618618618618,mv6_mw3ffc003fq924924924924924924,mv6_mw3ffc0000fc0q8a28a28a28a28a28a2,mv6_mwfc0fc0fc0000q249249249249249249,mv6_mw3f03f00003f000000q28a28a28a28a28a28a,mv6_mwfc0fc003f000000000q30c30c30c30c30c30c,mv6_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im16q8 : (child16q8.toFinset.image (relWord p9)) = node9.toFinset := by
  simp only [child16q8,node9, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv9_mwfff00000003f03fq861861861861861861,mv9_mw3ffffq618618618618618618,mv9_mw3ffc003fq924924924924924924,mv9_mw3ffc0000fc0q8a28a28a28a28a28a2,mv9_mwfc0fc0fc0000q249249249249249249,mv9_mwfff00000003f000q861861861861861861,mv9_mw3f03f00003f000000q28a28a28a28a28a28a,mv9_mwfc0fc003f000000000q30c30c30c30c30c30c,mv9_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im16q9 : (child16q9.toFinset.image (relWord p8)) = node2.toFinset := by
  simp only [child16q9,node2, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv8_mw3f03f00003f00003fq28a28a28a28a28a28a,mv8_mw3ffffq618618618618618618,mv8_mw3ffc003fq924924924924924924,mv8_mw3ffc0000fc0q8a28a28a28a28a28a2,mv8_mwfc0fc0fc0000q249249249249249249,mv8_mwfff00000003f000q861861861861861861,mv8_mwfc0fc003f000000000q30c30c30c30c30c30c,mv8_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im16q10 : (child16q10.toFinset.image (relWord p0)) = node8.toFinset := by
  simp only [child16q10,node8, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mw3f03f00003f00003fq28a28a28a28a28a28a,mv0_mw3fq0,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c,mv0_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im16q11 : (child16q11.toFinset.image (relWord p21)) = node9.toFinset := by
  simp only [child16q11,node9, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv21_mw3f03f00003f00003fq28a28a28a28a28a28a,mv21_mw3ffffq618618618618618618,mv21_mw3ffc003fq924924924924924924,mv21_mw3ffc0000fc0q8a28a28a28a28a28a2,mv21_mwfc0fc0fc0000q249249249249249249,mv21_mwfff00000003f000q861861861861861861,mv21_mw3f03f00003f000000q28a28a28a28a28a28a,mv21_mwfc0fc003f000000000q30c30c30c30c30c30c,mv21_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im16q12 : (child16q12.toFinset.image (relWord p6)) = node11.toFinset := by
  simp only [child16q12,node11, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv6_mwfc0fc003f00000003fq30c30c30c30c30c30c,mv6_mw3ffffq618618618618618618,mv6_mw3ffc003fq924924924924924924,mv6_mw3ffc0000fc0q8a28a28a28a28a28a2,mv6_mwfc0fc0fc0000q249249249249249249,mv6_mwfff00000003f000q861861861861861861,mv6_mw3f03f00003f000000q28a28a28a28a28a28a,mv6_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im16q13 : (child16q13.toFinset.image (relWord p6)) = node13.toFinset := by
  simp only [child16q13,node13, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv6_mwfc0fc003f00000003fq30c30c30c30c30c30c,mv6_mw3fq0,mv6_mw3ffffq618618618618618618,mv6_mw3ffc003fq924924924924924924,mv6_mw3ffc0000fc0q8a28a28a28a28a28a2,mv6_mwfc0fc0fc0000q249249249249249249,mv6_mwfff00000003f000q861861861861861861,mv6_mw3f03f00003f000000q28a28a28a28a28a28a,mv6_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im16q14 : (child16q14.toFinset.image (relWord p16)) = node14.toFinset := by
  simp only [child16q14,node14, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv16_mwfc0fc003f00000003fq30c30c30c30c30c30c,mv16_mw3ffffq618618618618618618,mv16_mw3ffc003fq924924924924924924,mv16_mw3ffc0000fc0q8a28a28a28a28a28a2,mv16_mwfc0fc0fc0000q249249249249249249,mv16_mwfff00000003f000q861861861861861861,mv16_mw3f03f00003f000000q28a28a28a28a28a28a,mv16_mwfc0fc003f000000000q30c30c30c30c30c30c,mv16_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im16q15 : (child16q15.toFinset.image (relWord p0)) = node11.toFinset := by
  simp only [child16q15,node11, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mwfff000fc000000003fqc30c30c30c30c30c30,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c]
  decide +kernel
private theorem im16q16 : (child16q16.toFinset.image (relWord p0)) = node13.toFinset := by
  simp only [child16q16,node13, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mwfff000fc000000003fqc30c30c30c30c30c30,mv0_mw3fq0,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c]
  decide +kernel
private theorem im16q17 : (child16q17.toFinset.image (relWord p40)) = node14.toFinset := by
  simp only [child16q17,node14, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv40_mwfff000fc000000003fqc30c30c30c30c30c30,mv40_mw3ffffq618618618618618618,mv40_mw3ffc003fq924924924924924924,mv40_mw3ffc0000fc0q8a28a28a28a28a28a2,mv40_mwfc0fc0fc0000q249249249249249249,mv40_mwfff00000003f000q861861861861861861,mv40_mw3f03f00003f000000q28a28a28a28a28a28a,mv40_mwfc0fc003f000000000q30c30c30c30c30c30c,mv40_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im16q18 : (child16q18.toFinset.image (relWord p6)) = node15.toFinset := by
  simp only [child16q18,node15, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv6_mwfc0fc003f00003ffffq71c71c71c71c71c71c,mv6_mw3fq0,mv6_mw3ffc003fq924924924924924924,mv6_mw3ffc0000fc0q8a28a28a28a28a28a2,mv6_mwfc0fc0fc0000q249249249249249249,mv6_mwfff00000003f000q861861861861861861,mv6_mw3f03f00003f000000q28a28a28a28a28a28a,mv6_mwfc0fc003f000000000q30c30c30c30c30c30c,mv6_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im16q19 : (child16q19.toFinset.image (relWord p0)) = node15.toFinset := by
  simp only [child16q19,node15, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mwfff000fc003ffc003fqd34d34d34d34d34d34,mv0_mw3fq0,mv0_mw3ffffq618618618618618618,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c,mv0_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
theorem excluded16 : ¬ Viable 9 node16 := by
  refine trace_close (r:=8) (xs:=node16) tab16 cert16 ?_ uniq16
  intro v hv
  simp only [tab16,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_viable_transport p21 sur21 im16q0 excluded2
  · exact not_viable_transport p7 sur7 im16q1 excluded8
  · exact not_viable_transport p8 sur8 im16q2 excluded9
  · exact not_viable_transport p9 sur9 im16q3 excluded2
  · exact not_viable_transport p1 sur1 im16q4 excluded8
  · exact not_viable_transport p20 sur20 im16q5 excluded9
  · exact not_viable_transport p20 sur20 im16q6 excluded2
  · exact not_viable_transport p6 sur6 im16q7 excluded8
  · exact not_viable_transport p9 sur9 im16q8 excluded9
  · exact not_viable_transport p8 sur8 im16q9 excluded2
  · exact not_viable_transport p0 sur0 im16q10 excluded8
  · exact not_viable_transport p21 sur21 im16q11 excluded9
  · exact not_viable_transport p6 sur6 im16q12 excluded11
  · exact not_viable_transport p6 sur6 im16q13 excluded13
  · exact not_viable_transport p16 sur16 im16q14 excluded14
  · exact not_viable_transport p0 sur0 im16q15 excluded11
  · exact not_viable_transport p0 sur0 im16q16 excluded13
  · exact not_viable_transport p40 sur40 im16q17 excluded14
  · exact not_viable_transport p6 sur6 im16q18 excluded15
  · exact not_viable_transport p0 sur0 im16q19 excluded15
theorem excluded17 : ¬ Viable 7 node17 := by
  refine trace_close (r:=6) (xs:=node17) tab17 cert17 ?_ uniq17
  intro v hv
  simp [tab17] at hv
private theorem im18q0 : (child18q0.toFinset.image (relWord p0)) = node17.toFinset := by
  simp only [child18q0,node17, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mwfff000fc0000fc0000qc30c30c30c30c30c30,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c]
  decide +kernel
theorem excluded18 : ¬ Viable 8 node18 := by
  refine trace_close (r:=7) (xs:=node18) tab18 cert18 ?_ uniq18
  intro v hv
  simp only [tab18,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl
  · exact not_viable_transport p0 sur0 im18q0 excluded17
theorem excluded19 : ¬ Viable 7 node19 := by
  refine trace_close (r:=6) (xs:=node19) tab19 cert19 ?_ uniq19
  intro v hv
  simp [tab19] at hv
private theorem im20q0 : (child20q0.toFinset.image (relWord p9)) = node17.toFinset := by
  simp only [child20q0,node17, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv9_mwfc0fc0fc003fq249249249249249249,mv9_mw3ffffq618618618618618618,mv9_mw3ffc003fq924924924924924924,mv9_mw3ffc0000fc0q8a28a28a28a28a28a2,mv9_mwfff00000003f000q861861861861861861,mv9_mw3f03f00003f000000q28a28a28a28a28a28a,mv9_mwfc0fc003f000000000q30c30c30c30c30c30c,mv9_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im20q1 : (child20q1.toFinset.image (relWord p8)) = node17.toFinset := by
  simp only [child20q1,node17, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv8_mw3f03f00003f00003fq28a28a28a28a28a28a,mv8_mw3ffffq618618618618618618,mv8_mw3ffc003fq924924924924924924,mv8_mw3ffc0000fc0q8a28a28a28a28a28a2,mv8_mwfc0fc0fc0000q249249249249249249,mv8_mwfff00000003f000q861861861861861861,mv8_mwfc0fc003f000000000q30c30c30c30c30c30c,mv8_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im20q2 : (child20q2.toFinset.image (relWord p6)) = node19.toFinset := by
  simp only [child20q2,node19, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv6_mwfc0fc003f00000003fq30c30c30c30c30c30c,mv6_mw3ffffq618618618618618618,mv6_mw3ffc003fq924924924924924924,mv6_mw3ffc0000fc0q8a28a28a28a28a28a2,mv6_mwfc0fc0fc0000q249249249249249249,mv6_mwfff00000003f000q861861861861861861,mv6_mw3f03f00003f000000q28a28a28a28a28a28a,mv6_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
theorem excluded20 : ¬ Viable 8 node20 := by
  refine trace_close (r:=7) (xs:=node20) tab20 cert20 ?_ uniq20
  intro v hv
  simp only [tab20,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl
  · exact not_viable_transport p9 sur9 im20q0 excluded17
  · exact not_viable_transport p8 sur8 im20q1 excluded17
  · exact not_viable_transport p6 sur6 im20q2 excluded19
theorem excluded21 : ¬ Viable 8 node21 := by
  refine trace_close (r:=7) (xs:=node21) tab21 cert21 ?_ uniq21
  intro v hv
  simp [tab21] at hv
theorem excluded22 : ¬ Viable 8 node22 := by
  refine trace_close (r:=7) (xs:=node22) tab22 cert22 ?_ uniq22
  intro v hv
  simp [tab22] at hv
theorem excluded23 : ¬ Viable 8 node23 := by
  refine trace_close (r:=7) (xs:=node23) tab23 cert23 ?_ uniq23
  intro v hv
  simp [tab23] at hv
private theorem im24q0 : (child24q0.toFinset.image (relWord p47)) = node18.toFinset := by
  simp only [child24q0,node18, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv47_mwfc0fc0ffffffq659659659659659659,mv47_mw3ffc003fq924924924924924924,mv47_mw3fffffffqf3cf3cf3cf3cf3cf3c,mv47_mw3ffc0000fc0q8a28a28a28a28a28a2,mv47_mwfc0fc0fc0000q249249249249249249,mv47_mwfff00000003f000q861861861861861861,mv47_mw3f03f00003f000000q28a28a28a28a28a28a,mv47_mwfc0fc003f000000000q30c30c30c30c30c30c,mv47_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im24q1 : (child24q1.toFinset.image (relWord p46)) = node18.toFinset := by
  simp only [child24q1,node18, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv46_mw3f03f00003f03ffffq69a69a69a69a69a69a,mv46_mw3ffc003fq924924924924924924,mv46_mw3fffffffqf3cf3cf3cf3cf3cf3c,mv46_mw3ffc0000fc0q8a28a28a28a28a28a2,mv46_mwfc0fc0fc0000q249249249249249249,mv46_mwfff00000003f000q861861861861861861,mv46_mw3f03f00003f000000q28a28a28a28a28a28a,mv46_mwfc0fc003f000000000q30c30c30c30c30c30c,mv46_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im24q2 : (child24q2.toFinset.image (relWord p23)) = node18.toFinset := by
  simp only [child24q2,node18, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv23_mw3fffffc0fffq9a69a69a69a69a69a6,mv23_mw3ffffq618618618618618618,mv23_mw3fffffffqf3cf3cf3cf3cf3cf3c,mv23_mw3ffc0000fc0q8a28a28a28a28a28a2,mv23_mwfc0fc0fc0000q249249249249249249,mv23_mwfff00000003f000q861861861861861861,mv23_mw3f03f00003f000000q28a28a28a28a28a28a,mv23_mwfc0fc003f000000000q30c30c30c30c30c30c,mv23_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im24q3 : (child24q3.toFinset.image (relWord p22)) = node18.toFinset := by
  simp only [child24q3,node18, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv22_mwfff00003ffff03fq965965965965965965,mv22_mw3ffffq618618618618618618,mv22_mw3fffffffqf3cf3cf3cf3cf3cf3c,mv22_mw3ffc0000fc0q8a28a28a28a28a28a2,mv22_mwfc0fc0fc0000q249249249249249249,mv22_mwfff00000003f000q861861861861861861,mv22_mw3f03f00003f000000q28a28a28a28a28a28a,mv22_mwfc0fc003f000000000q30c30c30c30c30c30c,mv22_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im24q4 : (child24q4.toFinset.image (relWord p8)) = node20.toFinset := by
  simp only [child24q4,node20, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv8_mwfc0q820820820820820820,mv8_mw3ffffq618618618618618618,mv8_mw3ffc003fq924924924924924924,mv8_mw3ffc0000fc0q8a28a28a28a28a28a2,mv8_mwfc0fc0fc0000q249249249249249249,mv8_mwfff00000003f000q861861861861861861,mv8_mw3f03f00003f000000q28a28a28a28a28a28a,mv8_mwfc0fc003f000000000q30c30c30c30c30c30c,mv8_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im24q5 : (child24q5.toFinset.image (relWord p0)) = node21.toFinset := by
  simp only [child24q5,node21, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mw3ffffffffffqfbefbefbefbefbefbe,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c,mv0_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im24q6 : (child24q6.toFinset.image (relWord p20)) = node20.toFinset := by
  simp only [child24q6,node20, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv20_mwfc0000q208208208208208208,mv20_mw3ffffq618618618618618618,mv20_mw3ffc003fq924924924924924924,mv20_mw3ffc0000fc0q8a28a28a28a28a28a2,mv20_mwfc0fc0fc0000q249249249249249249,mv20_mwfff00000003f000q861861861861861861,mv20_mw3f03f00003f000000q28a28a28a28a28a28a,mv20_mwfc0fc003f000000000q30c30c30c30c30c30c,mv20_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im24q7 : (child24q7.toFinset.image (relWord p6)) = node21.toFinset := by
  simp only [child24q7,node21, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv6_mwfc0fffffffffqf7df7df7df7df7df7d,mv6_mw3ffffq618618618618618618,mv6_mw3ffc003fq924924924924924924,mv6_mw3ffc0000fc0q8a28a28a28a28a28a2,mv6_mwfc0fc0fc0000q249249249249249249,mv6_mwfff00000003f000q861861861861861861,mv6_mw3f03f00003f000000q28a28a28a28a28a28a,mv6_mwfc0fc003f000000000q30c30c30c30c30c30c,mv6_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im24q8 : (child24q8.toFinset.image (relWord p9)) = node20.toFinset := by
  simp only [child24q8,node20, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv9_mw3f000q820820820820820820,mv9_mw3ffffq618618618618618618,mv9_mw3ffc003fq924924924924924924,mv9_mw3ffc0000fc0q8a28a28a28a28a28a2,mv9_mwfc0fc0fc0000q249249249249249249,mv9_mwfff00000003f000q861861861861861861,mv9_mw3f03f00003f000000q28a28a28a28a28a28a,mv9_mwfc0fc003f000000000q30c30c30c30c30c30c,mv9_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im24q9 : (child24q9.toFinset.image (relWord p1)) = node21.toFinset := by
  simp only [child24q9,node21, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1_mwfff00003fffffffqf7df7df7df7df7df7d,mv1_mw3ffffq618618618618618618,mv1_mw3ffc003fq924924924924924924,mv1_mw3ffc0000fc0q8a28a28a28a28a28a2,mv1_mwfc0fc0fc0000q249249249249249249,mv1_mwfff00000003f000q861861861861861861,mv1_mw3f03f00003f000000q28a28a28a28a28a28a,mv1_mwfc0fc003f000000000q30c30c30c30c30c30c,mv1_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im24q10 : (child24q10.toFinset.image (relWord p21)) = node20.toFinset := by
  simp only [child24q10,node20, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv21_mw3f000000q208208208208208208,mv21_mw3ffffq618618618618618618,mv21_mw3ffc003fq924924924924924924,mv21_mw3ffc0000fc0q8a28a28a28a28a28a2,mv21_mwfc0fc0fc0000q249249249249249249,mv21_mwfff00000003f000q861861861861861861,mv21_mw3f03f00003f000000q28a28a28a28a28a28a,mv21_mwfc0fc003f000000000q30c30c30c30c30c30c,mv21_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im24q11 : (child24q11.toFinset.image (relWord p7)) = node21.toFinset := by
  simp only [child24q11,node21, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv7_mw3f03f00003fffffffqfbefbefbefbefbefbe,mv7_mw3ffffq618618618618618618,mv7_mw3ffc003fq924924924924924924,mv7_mw3ffc0000fc0q8a28a28a28a28a28a2,mv7_mwfc0fc0fc0000q249249249249249249,mv7_mwfff00000003f000q861861861861861861,mv7_mw3f03f00003f000000q28a28a28a28a28a28a,mv7_mwfc0fc003f000000000q30c30c30c30c30c30c,mv7_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im24q12 : (child24q12.toFinset.image (relWord p4)) = node22.toFinset := by
  simp only [child24q12,node22, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv4_mw0q30c30c30c30c30c30c,mv4_mw3ffffq618618618618618618,mv4_mw3ffc003fq924924924924924924,mv4_mw3ffc0000fc0q8a28a28a28a28a28a2,mv4_mwfc0fc0fc0000q249249249249249249,mv4_mwfff00000003f000q861861861861861861,mv4_mw3f03f00003f000000q28a28a28a28a28a28a,mv4_mwfc0fc003f000000000q30c30c30c30c30c30c,mv4_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im24q13 : (child24q13.toFinset.image (relWord p4)) = node23.toFinset := by
  simp only [child24q13,node23, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv4_mwfc0fc003f03fffffffqf3cf3cf3cf3cf3cf3c,mv4_mw3ffffq618618618618618618,mv4_mw3ffc003fq924924924924924924,mv4_mw3ffc0000fc0q8a28a28a28a28a28a2,mv4_mwfc0fc0fc0000q249249249249249249,mv4_mwfff00000003f000q861861861861861861,mv4_mw3f03f00003f000000q28a28a28a28a28a28a,mv4_mwfc0fc003f000000000q30c30c30c30c30c30c,mv4_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im24q14 : (child24q14.toFinset.image (relWord p24)) = node22.toFinset := by
  simp only [child24q14,node22, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv24_mw0qc30c30c30c30c30c30,mv24_mw3ffffq618618618618618618,mv24_mw3ffc003fq924924924924924924,mv24_mw3ffc0000fc0q8a28a28a28a28a28a2,mv24_mwfc0fc0fc0000q249249249249249249,mv24_mwfff00000003f000q861861861861861861,mv24_mw3f03f00003f000000q28a28a28a28a28a28a,mv24_mwfc0fc003f000000000q30c30c30c30c30c30c,mv24_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im24q15 : (child24q15.toFinset.image (relWord p28)) = node23.toFinset := by
  simp only [child24q15,node23, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv28_mwfff000fc003fffffffqf3cf3cf3cf3cf3cf3c,mv28_mw3ffffq618618618618618618,mv28_mw3ffc003fq924924924924924924,mv28_mw3ffc0000fc0q8a28a28a28a28a28a2,mv28_mwfc0fc0fc0000q249249249249249249,mv28_mwfff00000003f000q861861861861861861,mv28_mw3f03f00003f000000q28a28a28a28a28a28a,mv28_mwfc0fc003f000000000q30c30c30c30c30c30c,mv28_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
theorem excluded24 : ¬ Viable 9 node24 := by
  refine trace_close (r:=8) (xs:=node24) tab24 cert24 ?_ uniq24
  intro v hv
  simp only [tab24,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_viable_transport p47 sur47 im24q0 excluded18
  · exact not_viable_transport p46 sur46 im24q1 excluded18
  · exact not_viable_transport p23 sur23 im24q2 excluded18
  · exact not_viable_transport p22 sur22 im24q3 excluded18
  · exact not_viable_transport p8 sur8 im24q4 excluded20
  · exact not_viable_transport p0 sur0 im24q5 excluded21
  · exact not_viable_transport p20 sur20 im24q6 excluded20
  · exact not_viable_transport p6 sur6 im24q7 excluded21
  · exact not_viable_transport p9 sur9 im24q8 excluded20
  · exact not_viable_transport p1 sur1 im24q9 excluded21
  · exact not_viable_transport p21 sur21 im24q10 excluded20
  · exact not_viable_transport p7 sur7 im24q11 excluded21
  · exact not_viable_transport p4 sur4 im24q12 excluded22
  · exact not_viable_transport p4 sur4 im24q13 excluded23
  · exact not_viable_transport p24 sur24 im24q14 excluded22
  · exact not_viable_transport p28 sur28 im24q15 excluded23
theorem excluded25 : ¬ Viable 8 node25 := by
  refine trace_close (r:=7) (xs:=node25) tab25 cert25 ?_ uniq25
  intro v hv
  simp [tab25] at hv
private theorem im26q0 : (child26q0.toFinset.image (relWord p6)) = node25.toFinset := by
  simp only [child26q0,node25, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv6_mw3ffc003fqb2cb2cb2cb2cb2cb2c,mv6_mw3ffffq618618618618618618,mv6_mw3ffc003fq924924924924924924,mv6_mw3ffc0000fc0q8a28a28a28a28a28a2,mv6_mwfc0fc0fc0000q249249249249249249,mv6_mwfff00000003f000q861861861861861861,mv6_mw3f03f00003f000000q28a28a28a28a28a28a,mv6_mwfc0fc003f000000000q30c30c30c30c30c30c,mv6_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im26q1 : (child26q1.toFinset.image (relWord p8)) = node25.toFinset := by
  simp only [child26q1,node25, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv8_mw3ffc0000fc0qaaaaaaaaaaaaaaaaaa,mv8_mw3ffffq618618618618618618,mv8_mw3ffc003fq924924924924924924,mv8_mw3ffc0000fc0q8a28a28a28a28a28a2,mv8_mwfc0fc0fc0000q249249249249249249,mv8_mwfff00000003f000q861861861861861861,mv8_mw3f03f00003f000000q28a28a28a28a28a28a,mv8_mwfc0fc003f000000000q30c30c30c30c30c30c,mv8_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im26q2 : (child26q2.toFinset.image (relWord p9)) = node25.toFinset := by
  simp only [child26q2,node25, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv9_mwfff00000003f000qa69a69a69a69a69a69,mv9_mw3ffffq618618618618618618,mv9_mw3ffc003fq924924924924924924,mv9_mw3ffc0000fc0q8a28a28a28a28a28a2,mv9_mwfc0fc0fc0000q249249249249249249,mv9_mwfff00000003f000q861861861861861861,mv9_mw3f03f00003f000000q28a28a28a28a28a28a,mv9_mwfc0fc003f000000000q30c30c30c30c30c30c,mv9_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im26q3 : (child26q3.toFinset.image (relWord p42)) = node25.toFinset := by
  simp only [child26q3,node25, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv42_mwfff000fc0000000000qe38e38e38e38e38e38,mv42_mw3ffffq618618618618618618,mv42_mw3ffc003fq924924924924924924,mv42_mw3ffc0000fc0q8a28a28a28a28a28a2,mv42_mwfc0fc0fc0000q249249249249249249,mv42_mwfff00000003f000q861861861861861861,mv42_mw3f03f00003f000000q28a28a28a28a28a28a,mv42_mwfc0fc003f000000000q30c30c30c30c30c30c,mv42_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
theorem excluded26 : ¬ Viable 9 node26 := by
  refine trace_close (r:=8) (xs:=node26) tab26 cert26 ?_ uniq26
  intro v hv
  simp only [tab26,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact not_viable_transport p6 sur6 im26q0 excluded25
  · exact not_viable_transport p8 sur8 im26q1 excluded25
  · exact not_viable_transport p9 sur9 im26q2 excluded25
  · exact not_viable_transport p42 sur42 im26q3 excluded25
theorem excluded27 : ¬ Viable 7 node27 := by
  refine trace_close (r:=6) (xs:=node27) tab27 cert27 ?_ uniq27
  intro v hv
  simp [tab27] at hv
theorem excluded28 : ¬ Viable 7 node28 := by
  refine trace_close (r:=6) (xs:=node28) tab28 cert28 ?_ uniq28
  intro v hv
  simp [tab28] at hv
theorem excluded29 : ¬ Viable 7 node29 := by
  refine trace_close (r:=6) (xs:=node29) tab29 cert29 ?_ uniq29
  intro v hv
  simp [tab29] at hv
theorem excluded30 : ¬ Viable 7 node30 := by
  refine trace_close (r:=6) (xs:=node30) tab30 cert30 ?_ uniq30
  intro v hv
  simp [tab30] at hv
private theorem im31q0 : (child31q0.toFinset.image (relWord p23)) = node17.toFinset := by
  simp only [child31q0,node17, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv23_mw3ffc0fffq924924924924924924,mv23_mw3ffffq618618618618618618,mv23_mw3ffc0000fc0q8a28a28a28a28a28a2,mv23_mwfc0fc0fc0000q249249249249249249,mv23_mwfff00000003f000q861861861861861861,mv23_mw3f03f00003f000000q28a28a28a28a28a28a,mv23_mwfc0fc003f000000000q30c30c30c30c30c30c,mv23_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im31q1 : (child31q1.toFinset.image (relWord p21)) = node17.toFinset := by
  simp only [child31q1,node17, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv21_mw3ffc0000fffq8a28a28a28a28a28a2,mv21_mw3ffffq618618618618618618,mv21_mw3ffc003fq924924924924924924,mv21_mwfc0fc0fc0000q249249249249249249,mv21_mwfff00000003f000q861861861861861861,mv21_mw3f03f00003f000000q28a28a28a28a28a28a,mv21_mwfc0fc003f000000000q30c30c30c30c30c30c,mv21_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im31q2 : (child31q2.toFinset.image (relWord p9)) = node27.toFinset := by
  simp only [child31q2,node27, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv9_mwfc0fc0fc0fffq249249249249249249,mv9_mw3ffffq618618618618618618,mv9_mw3ffc003fq924924924924924924,mv9_mw3ffc0000fc0q8a28a28a28a28a28a2,mv9_mwfff00000003f000q861861861861861861,mv9_mw3f03f00003f000000q28a28a28a28a28a28a,mv9_mwfc0fc003f000000000q30c30c30c30c30c30c,mv9_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im31q3 : (child31q3.toFinset.image (relWord p18)) = node28.toFinset := by
  simp only [child31q3,node28, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv18_mwfff00000003ffffq861861861861861861,mv18_mw3ffffq618618618618618618,mv18_mw3ffc003fq924924924924924924,mv18_mw3ffc0000fc0q8a28a28a28a28a28a2,mv18_mwfc0fc0fc0000q249249249249249249,mv18_mw3f03f00003f000000q28a28a28a28a28a28a,mv18_mwfc0fc003f000000000q30c30c30c30c30c30c,mv18_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im31q4 : (child31q4.toFinset.image (relWord p8)) = node29.toFinset := by
  simp only [child31q4,node29, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv8_mw3f03f00003f000fffq28a28a28a28a28a28a,mv8_mw3ffffq618618618618618618,mv8_mw3ffc003fq924924924924924924,mv8_mw3ffc0000fc0q8a28a28a28a28a28a2,mv8_mwfc0fc0fc0000q249249249249249249,mv8_mwfff00000003f000q861861861861861861,mv8_mwfc0fc003f000000000q30c30c30c30c30c30c,mv8_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im31q5 : (child31q5.toFinset.image (relWord p6)) = node29.toFinset := by
  simp only [child31q5,node29, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv6_mwfc0fc003f000000fffq30c30c30c30c30c30c,mv6_mw3ffffq618618618618618618,mv6_mw3ffc003fq924924924924924924,mv6_mw3ffc0000fc0q8a28a28a28a28a28a2,mv6_mwfc0fc0fc0000q249249249249249249,mv6_mwfff00000003f000q861861861861861861,mv6_mw3f03f00003f000000q28a28a28a28a28a28a,mv6_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im31q6 : (child31q6.toFinset.image (relWord p0)) = node30.toFinset := by
  simp only [child31q6,node30, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mwfff000fc0000000fffqc30c30c30c30c30c30,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c]
  decide +kernel
theorem excluded31 : ¬ Viable 8 node31 := by
  refine trace_close (r:=7) (xs:=node31) tab31 cert31 ?_ uniq31
  intro v hv
  simp only [tab31,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_viable_transport p23 sur23 im31q0 excluded17
  · exact not_viable_transport p21 sur21 im31q1 excluded17
  · exact not_viable_transport p9 sur9 im31q2 excluded27
  · exact not_viable_transport p18 sur18 im31q3 excluded28
  · exact not_viable_transport p8 sur8 im31q4 excluded29
  · exact not_viable_transport p6 sur6 im31q5 excluded29
  · exact not_viable_transport p0 sur0 im31q6 excluded30
theorem excluded32 : ¬ Viable 7 node32 := by
  refine trace_close (r:=6) (xs:=node32) tab32 cert32 ?_ uniq32
  intro v hv
  simp [tab32] at hv
theorem excluded33 : ¬ Viable 7 node33 := by
  refine trace_close (r:=6) (xs:=node33) tab33 cert33 ?_ uniq33
  intro v hv
  simp [tab33] at hv
private theorem im34q0 : (child34q0.toFinset.image (relWord p9)) = node32.toFinset := by
  simp only [child34q0,node32, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv9_mw3fffffc0fffq9a69a69a69a69a69a6,mv9_mw3ffffq618618618618618618,mv9_mwfc0fc0fc0000q249249249249249249,mv9_mwfff00000003f000q861861861861861861,mv9_mw3f03f00003f000000q28a28a28a28a28a28a,mv9_mwfc0fc003f000000000q30c30c30c30c30c30c,mv9_mwfff000fc003ffc003fqd34d34d34d34d34d34,mv9_mwfff000ffffc0000fc0qcb2cb2cb2cb2cb2cb2]
  decide +kernel
private theorem im34q1 : (child34q1.toFinset.image (relWord p0)) = node33.toFinset := by
  simp only [child34q1,node33, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mwfff000fc0000000000qc30c30c30c30c30c30,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c]
  decide +kernel
theorem excluded34 : ¬ Viable 8 node34 := by
  refine trace_close (r:=7) (xs:=node34) tab34 cert34 ?_ uniq34
  intro v hv
  simp only [tab34,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl
  · exact not_viable_transport p9 sur9 im34q0 excluded32
  · exact not_viable_transport p0 sur0 im34q1 excluded33
private theorem im35q0 : (child35q0.toFinset.image (relWord p0)) = node19.toFinset := by
  simp only [child35q0,node19, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mwfff000fc000000003fqc30c30c30c30c30c30,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c]
  decide +kernel
theorem excluded35 : ¬ Viable 8 node35 := by
  refine trace_close (r:=7) (xs:=node35) tab35 cert35 ?_ uniq35
  intro v hv
  simp only [tab35,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl
  · exact not_viable_transport p0 sur0 im35q0 excluded19
theorem excluded36 : ¬ Viable 8 node36 := by
  refine trace_close (r:=7) (xs:=node36) tab36 cert36 ?_ uniq36
  intro v hv
  simp [tab36] at hv
theorem excluded37 : ¬ Viable 7 node37 := by
  refine trace_close (r:=6) (xs:=node37) tab37 cert37 ?_ uniq37
  intro v hv
  simp [tab37] at hv
private theorem im38q0 : (child38q0.toFinset.image (relWord p0)) = node37.toFinset := by
  simp only [child38q0,node37, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mw3ffffq0,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c,mv0_mwfff000fc0000000000qc30c30c30c30c30c30]
theorem excluded38 : ¬ Viable 8 node38 := by
  refine trace_close (r:=7) (xs:=node38) tab38 cert38 ?_ uniq38
  intro v hv
  simp only [tab38,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl
  · exact not_viable_transport p0 sur0 im38q0 excluded37
private theorem im39q0 : (child39q0.toFinset.image (relWord p6)) = node19.toFinset := by
  simp only [child39q0,node19, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv6_mwfc0fc003f00000003fq30c30c30c30c30c30c,mv6_mw3ffffq618618618618618618,mv6_mw3ffc003fq924924924924924924,mv6_mw3ffc0000fc0q8a28a28a28a28a28a2,mv6_mwfc0fc0fc0000q249249249249249249,mv6_mwfff00000003f000q861861861861861861,mv6_mw3f03f00003f000000q28a28a28a28a28a28a,mv6_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
theorem excluded39 : ¬ Viable 8 node39 := by
  refine trace_close (r:=7) (xs:=node39) tab39 cert39 ?_ uniq39
  intro v hv
  simp only [tab39,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl
  · exact not_viable_transport p6 sur6 im39q0 excluded19
private theorem im40q0 : (child40q0.toFinset.image (relWord p23)) = node18.toFinset := by
  simp only [child40q0,node18, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv23_mw3fffffffqf3cf3cf3cf3cf3cf3c,mv23_mw3ffffq618618618618618618,mv23_mw3ffc0000fc0q8a28a28a28a28a28a2,mv23_mw3fffffc0fffq9a69a69a69a69a69a6,mv23_mwfc0fc0fc0000q249249249249249249,mv23_mwfff00000003f000q861861861861861861,mv23_mw3f03f00003f000000q28a28a28a28a28a28a,mv23_mwfc0fc003f000000000q30c30c30c30c30c30c,mv23_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q1 : (child40q1.toFinset.image (relWord p21)) = node18.toFinset := by
  simp only [child40q1,node18, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv21_mw3ffc003ffffqebaebaebaebaebaeba,mv21_mw3ffffq618618618618618618,mv21_mw3ffc003fq924924924924924924,mv21_mw3fffffc0fffq9a69a69a69a69a69a6,mv21_mwfc0fc0fc0000q249249249249249249,mv21_mwfff00000003f000q861861861861861861,mv21_mw3f03f00003f000000q28a28a28a28a28a28a,mv21_mwfc0fc003f000000000q30c30c30c30c30c30c,mv21_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q2 : (child40q2.toFinset.image (relWord p0)) = node31.toFinset := by
  simp only [child40q2,node31, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mwfffq0,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c,mv0_mwfff000fc0000000000qc30c30c30c30c30c30]
private theorem im40q3 : (child40q3.toFinset.image (relWord p0)) = node21.toFinset := by
  simp only [child40q3,node21, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mw3ffffffffffqfbefbefbefbefbefbe,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c,mv0_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q4 : (child40q4.toFinset.image (relWord p33)) = node18.toFinset := by
  simp only [child40q4,node18, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv33_mwfc0ffffc003fqb6db6db6db6db6db6d,mv33_mw3ffffq618618618618618618,mv33_mw3ffc0000fc0q8a28a28a28a28a28a2,mv33_mw3fffffc0fffq9a69a69a69a69a69a6,mv33_mwfc0fc0fc0000q249249249249249249,mv33_mwfff00000003f000q861861861861861861,mv33_mw3f03f00003f000000q28a28a28a28a28a28a,mv33_mwfc0fc003f000000000q30c30c30c30c30c30c,mv33_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q5 : (child40q5.toFinset.image (relWord p22)) = node34.toFinset := by
  simp only [child40q5,node34, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv22_mwfff00003ffff03fq965965965965965965,mv22_mw3ffffq618618618618618618,mv22_mw3ffc0000fc0q8a28a28a28a28a28a2,mv22_mw3fffffc0fffq9a69a69a69a69a69a6,mv22_mwfc0fc0fc0000q249249249249249249,mv22_mwfff00000003f000q861861861861861861,mv22_mw3f03f00003f000000q28a28a28a28a28a28a,mv22_mwfc0fc003f000000000q30c30c30c30c30c30c,mv22_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q6 : (child40q6.toFinset.image (relWord p21)) = node15.toFinset := by
  simp only [child40q6,node15, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv21_mw3f000000q0,mv21_mw3ffffq618618618618618618,mv21_mw3ffc0000fc0q8a28a28a28a28a28a2,mv21_mw3fffffc0fffq9a69a69a69a69a69a6,mv21_mwfc0fc0fc0000q249249249249249249,mv21_mwfff00000003f000q861861861861861861,mv21_mw3f03f00003f000000q28a28a28a28a28a28a,mv21_mwfc0fc003f000000000q30c30c30c30c30c30c,mv21_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q7 : (child40q7.toFinset.image (relWord p23)) = node35.toFinset := by
  simp only [child40q7,node35, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv23_mwfc0fc003f03ffc003fqb2cb2cb2cb2cb2cb2c,mv23_mw3ffffq618618618618618618,mv23_mw3ffc0000fc0q8a28a28a28a28a28a2,mv23_mw3fffffc0fffq9a69a69a69a69a69a6,mv23_mwfc0fc0fc0000q249249249249249249,mv23_mwfff00000003f000q861861861861861861,mv23_mw3f03f00003f000000q28a28a28a28a28a28a,mv23_mwfc0fc003f000000000q30c30c30c30c30c30c,mv23_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q8 : (child40q8.toFinset.image (relWord p33)) = node34.toFinset := by
  simp only [child40q8,node34, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv33_mwfff000fc003ffc003fqd34d34d34d34d34d34,mv33_mw3ffffq618618618618618618,mv33_mw3ffc0000fc0q8a28a28a28a28a28a2,mv33_mw3fffffc0fffq9a69a69a69a69a69a6,mv33_mwfc0fc0fc0000q249249249249249249,mv33_mwfff00000003f000q861861861861861861,mv33_mw3f03f00003f000000q28a28a28a28a28a28a,mv33_mwfc0fc003f000000000q30c30c30c30c30c30c,mv33_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q9 : (child40q9.toFinset.image (relWord p35)) = node18.toFinset := by
  simp only [child40q9,node18, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv35_mwffffc0fc0fc0qaebaebaebaebaebaeb,mv35_mw3ffffq618618618618618618,mv35_mw3ffc003fq924924924924924924,mv35_mw3fffffc0fffq9a69a69a69a69a69a6,mv35_mwfc0fc0fc0000q249249249249249249,mv35_mwfff00000003f000q861861861861861861,mv35_mw3f03f00003f000000q28a28a28a28a28a28a,mv35_mwfc0fc003f000000000q30c30c30c30c30c30c,mv35_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q10 : (child40q10.toFinset.image (relWord p19)) = node34.toFinset := by
  simp only [child40q10,node34, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv19_mwfff03ffc003ffc0q8e38e38e38e38e38e3,mv19_mw3ffffq618618618618618618,mv19_mw3ffc003fq924924924924924924,mv19_mw3fffffc0fffq9a69a69a69a69a69a6,mv19_mwfc0fc0fc0000q249249249249249249,mv19_mwfff00000003f000q861861861861861861,mv19_mw3f03f00003f000000q28a28a28a28a28a28a,mv19_mwfc0fc003f000000000q30c30c30c30c30c30c,mv19_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q11 : (child40q11.toFinset.image (relWord p21)) = node35.toFinset := by
  simp only [child40q11,node35, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv21_mw3f03f03ffff000fc0qaaaaaaaaaaaaaaaaaa,mv21_mw3ffffq618618618618618618,mv21_mw3ffc003fq924924924924924924,mv21_mw3fffffc0fffq9a69a69a69a69a69a6,mv21_mwfc0fc0fc0000q249249249249249249,mv21_mwfff00000003f000q861861861861861861,mv21_mw3f03f00003f000000q28a28a28a28a28a28a,mv21_mwfc0fc003f000000000q30c30c30c30c30c30c,mv21_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q12 : (child40q12.toFinset.image (relWord p23)) = node15.toFinset := by
  simp only [child40q12,node15, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv23_mw3f000000000q0,mv23_mw3ffffq618618618618618618,mv23_mw3ffc003fq924924924924924924,mv23_mw3fffffc0fffq9a69a69a69a69a69a6,mv23_mwfc0fc0fc0000q249249249249249249,mv23_mwfff00000003f000q861861861861861861,mv23_mw3f03f00003f000000q28a28a28a28a28a28a,mv23_mwfc0fc003f000000000q30c30c30c30c30c30c,mv23_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q13 : (child40q13.toFinset.image (relWord p35)) = node34.toFinset := by
  simp only [child40q13,node34, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv35_mwfff000ffffc0000fc0qcb2cb2cb2cb2cb2cb2,mv35_mw3ffffq618618618618618618,mv35_mw3ffc003fq924924924924924924,mv35_mw3fffffc0fffq9a69a69a69a69a69a6,mv35_mwfc0fc0fc0000q249249249249249249,mv35_mwfff00000003f000q861861861861861861,mv35_mw3f03f00003f000000q28a28a28a28a28a28a,mv35_mwfc0fc003f000000000q30c30c30c30c30c30c,mv35_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q14 : (child40q14.toFinset.image (relWord p18)) = node31.toFinset := by
  simp only [child40q14,node31, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv18_mwfc0fc0000q0,mv18_mw3ffffq618618618618618618,mv18_mw3ffc003fq924924924924924924,mv18_mw3ffc0000fc0q8a28a28a28a28a28a2,mv18_mwfc0fc0fc0000q249249249249249249,mv18_mwfff00000003f000q861861861861861861,mv18_mw3f03f00003f000000q28a28a28a28a28a28a,mv18_mwfc0fc003f000000000q30c30c30c30c30c30c,mv18_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q15 : (child40q15.toFinset.image (relWord p18)) = node21.toFinset := by
  simp only [child40q15,node21, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv18_mwfffffffc0fffqbefbefbefbefbefbef,mv18_mw3ffffq618618618618618618,mv18_mw3ffc003fq924924924924924924,mv18_mw3ffc0000fc0q8a28a28a28a28a28a2,mv18_mwfc0fc0fc0000q249249249249249249,mv18_mwfff00000003f000q861861861861861861,mv18_mw3f03f00003f000000q28a28a28a28a28a28a,mv18_mwfc0fc003f000000000q30c30c30c30c30c30c,mv18_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q16 : (child40q16.toFinset.image (relWord p6)) = node36.toFinset := by
  simp only [child40q16,node36, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv6_mw0q820820820820820820,mv6_mw3ffffq618618618618618618,mv6_mw3ffc003fq924924924924924924,mv6_mw3ffc0000fc0q8a28a28a28a28a28a2,mv6_mwfc0fc0fc0000q249249249249249249,mv6_mwfff00000003f000q861861861861861861,mv6_mw3f03f00003f000000q28a28a28a28a28a28a,mv6_mwfc0fc003f000000000q30c30c30c30c30c30c,mv6_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q17 : (child40q17.toFinset.image (relWord p0)) = node38.toFinset := by
  simp only [child40q17,node38, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mwfff03ffffffffffq9e79e79e79e79e79e7,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c,mv0_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q18 : (child40q18.toFinset.image (relWord p15)) = node39.toFinset := by
  simp only [child40q18,node39, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv15_mw3f000000q82082082082082082,mv15_mw3ffffq618618618618618618,mv15_mw3ffc003fq924924924924924924,mv15_mw3ffc0000fc0q8a28a28a28a28a28a2,mv15_mwfc0fc0fc0000q249249249249249249,mv15_mwfff00000003f000q861861861861861861,mv15_mw3f03f00003f000000q28a28a28a28a28a28a,mv15_mwfc0fc003f000000000q30c30c30c30c30c30c,mv15_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q19 : (child40q19.toFinset.image (relWord p6)) = node23.toFinset := by
  simp only [child40q19,node23, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv6_mw3f03f03fffffc0fffqbaebaebaebaebaebae,mv6_mw3ffffq618618618618618618,mv6_mw3ffc003fq924924924924924924,mv6_mw3ffc0000fc0q8a28a28a28a28a28a2,mv6_mwfc0fc0fc0000q249249249249249249,mv6_mwfff00000003f000q861861861861861861,mv6_mw3f03f00003f000000q28a28a28a28a28a28a,mv6_mwfc0fc003f000000000q30c30c30c30c30c30c,mv6_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q20 : (child40q20.toFinset.image (relWord p17)) = node39.toFinset := by
  simp only [child40q20,node39, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv17_mw3f000000000q104104104104104104,mv17_mw3ffffq618618618618618618,mv17_mw3ffc003fq924924924924924924,mv17_mw3ffc0000fc0q8a28a28a28a28a28a2,mv17_mwfc0fc0fc0000q249249249249249249,mv17_mwfff00000003f000q861861861861861861,mv17_mw3f03f00003f000000q28a28a28a28a28a28a,mv17_mwfc0fc003f000000000q30c30c30c30c30c30c,mv17_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q21 : (child40q21.toFinset.image (relWord p8)) = node23.toFinset := by
  simp only [child40q21,node23, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv8_mwfc0fc003fffffc0fffqbaebaebaebaebaebae,mv8_mw3ffffq618618618618618618,mv8_mw3ffc003fq924924924924924924,mv8_mw3ffc0000fc0q8a28a28a28a28a28a2,mv8_mwfc0fc0fc0000q249249249249249249,mv8_mwfff00000003f000q861861861861861861,mv8_mw3f03f00003f000000q28a28a28a28a28a28a,mv8_mwfc0fc003f000000000q30c30c30c30c30c30c,mv8_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im40q22 : (child40q22.toFinset.image (relWord p18)) = node38.toFinset := by
  simp only [child40q22,node38, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv18_mwfff000fffffffc0fffqdb6db6db6db6db6db6,mv18_mw3ffffq618618618618618618,mv18_mw3ffc003fq924924924924924924,mv18_mw3ffc0000fc0q8a28a28a28a28a28a2,mv18_mwfc0fc0fc0000q249249249249249249,mv18_mwfff00000003f000q861861861861861861,mv18_mw3f03f00003f000000q28a28a28a28a28a28a,mv18_mwfc0fc003f000000000q30c30c30c30c30c30c,mv18_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
theorem excluded40 : ¬ Viable 9 node40 := by
  refine trace_close (r:=8) (xs:=node40) tab40 cert40 ?_ uniq40
  intro v hv
  simp only [tab40,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_viable_transport p23 sur23 im40q0 excluded18
  · exact not_viable_transport p21 sur21 im40q1 excluded18
  · exact not_viable_transport p0 sur0 im40q2 excluded31
  · exact not_viable_transport p0 sur0 im40q3 excluded21
  · exact not_viable_transport p33 sur33 im40q4 excluded18
  · exact not_viable_transport p22 sur22 im40q5 excluded34
  · exact not_viable_transport p21 sur21 im40q6 excluded15
  · exact not_viable_transport p23 sur23 im40q7 excluded35
  · exact not_viable_transport p33 sur33 im40q8 excluded34
  · exact not_viable_transport p35 sur35 im40q9 excluded18
  · exact not_viable_transport p19 sur19 im40q10 excluded34
  · exact not_viable_transport p21 sur21 im40q11 excluded35
  · exact not_viable_transport p23 sur23 im40q12 excluded15
  · exact not_viable_transport p35 sur35 im40q13 excluded34
  · exact not_viable_transport p18 sur18 im40q14 excluded31
  · exact not_viable_transport p18 sur18 im40q15 excluded21
  · exact not_viable_transport p6 sur6 im40q16 excluded36
  · exact not_viable_transport p0 sur0 im40q17 excluded38
  · exact not_viable_transport p15 sur15 im40q18 excluded39
  · exact not_viable_transport p6 sur6 im40q19 excluded23
  · exact not_viable_transport p17 sur17 im40q20 excluded39
  · exact not_viable_transport p8 sur8 im40q21 excluded23
  · exact not_viable_transport p18 sur18 im40q22 excluded38
theorem excluded41 : ¬ Viable 8 node41 := by
  refine trace_close (r:=7) (xs:=node41) tab41 cert41 ?_ uniq41
  intro v hv
  simp [tab41] at hv
private theorem im42q0 : (child42q0.toFinset.image (relWord p0)) = node41.toFinset := by
  simp only [child42q0,node41, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mw3ffffq659659659659659659,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c,mv0_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im42q1 : (child42q1.toFinset.image (relWord p7)) = node41.toFinset := by
  simp only [child42q1,node41, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv7_mw3ffc003fq965965965965965965,mv7_mw3ffffq618618618618618618,mv7_mw3ffc003fq924924924924924924,mv7_mw3ffc0000fc0q8a28a28a28a28a28a2,mv7_mwfc0fc0fc0000q249249249249249249,mv7_mwfff00000003f000q861861861861861861,mv7_mw3f03f00003f000000q28a28a28a28a28a28a,mv7_mwfc0fc003f000000000q30c30c30c30c30c30c,mv7_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im42q2 : (child42q2.toFinset.image (relWord p10)) = node41.toFinset := by
  simp only [child42q2,node41, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv10_mw3ffc0000fc0q8e38e38e38e38e38e3,mv10_mw3ffffq618618618618618618,mv10_mw3ffc003fq924924924924924924,mv10_mw3ffc0000fc0q8a28a28a28a28a28a2,mv10_mwfc0fc0fc0000q249249249249249249,mv10_mwfff00000003f000q861861861861861861,mv10_mw3f03f00003f000000q28a28a28a28a28a28a,mv10_mwfc0fc003f000000000q30c30c30c30c30c30c,mv10_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im42q3 : (child42q3.toFinset.image (relWord p35)) = node41.toFinset := by
  simp only [child42q3,node41, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv35_mw3f03f00003f000000q2cb2cb2cb2cb2cb2cb,mv35_mw3ffffq618618618618618618,mv35_mw3ffc003fq924924924924924924,mv35_mw3ffc0000fc0q8a28a28a28a28a28a2,mv35_mwfc0fc0fc0000q249249249249249249,mv35_mwfff00000003f000q861861861861861861,mv35_mw3f03f00003f000000q28a28a28a28a28a28a,mv35_mwfc0fc003f000000000q30c30c30c30c30c30c,mv35_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im42q4 : (child42q4.toFinset.image (relWord p33)) = node41.toFinset := by
  simp only [child42q4,node41, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv33_mwfc0fc003f000000000q34d34d34d34d34d34d,mv33_mw3ffffq618618618618618618,mv33_mw3ffc003fq924924924924924924,mv33_mw3ffc0000fc0q8a28a28a28a28a28a2,mv33_mwfc0fc0fc0000q249249249249249249,mv33_mwfff00000003f000q861861861861861861,mv33_mw3f03f00003f000000q28a28a28a28a28a28a,mv33_mwfc0fc003f000000000q30c30c30c30c30c30c,mv33_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im42q5 : (child42q5.toFinset.image (relWord p42)) = node41.toFinset := by
  simp only [child42q5,node41, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv42_mwfff000fc0000000000qc71c71c71c71c71c71,mv42_mw3ffffq618618618618618618,mv42_mw3ffc003fq924924924924924924,mv42_mw3ffc0000fc0q8a28a28a28a28a28a2,mv42_mwfc0fc0fc0000q249249249249249249,mv42_mwfff00000003f000q861861861861861861,mv42_mw3f03f00003f000000q28a28a28a28a28a28a,mv42_mwfc0fc003f000000000q30c30c30c30c30c30c,mv42_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
theorem excluded42 : ¬ Viable 9 node42 := by
  refine trace_close (r:=8) (xs:=node42) tab42 cert42 ?_ uniq42
  intro v hv
  simp only [tab42,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_viable_transport p0 sur0 im42q0 excluded41
  · exact not_viable_transport p7 sur7 im42q1 excluded41
  · exact not_viable_transport p10 sur10 im42q2 excluded41
  · exact not_viable_transport p35 sur35 im42q3 excluded41
  · exact not_viable_transport p33 sur33 im42q4 excluded41
  · exact not_viable_transport p42 sur42 im42q5 excluded41
private theorem im43q0 : (child43q0.toFinset.image (relWord p9)) = node35.toFinset := by
  simp only [child43q0,node35, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv9_mwfc0fc0ffffffq659659659659659659,mv9_mw3ffffq618618618618618618,mv9_mw3ffc003fq924924924924924924,mv9_mw3ffc0000fc0q8a28a28a28a28a28a2,mv9_mwfff00000003f000q861861861861861861,mv9_mwffffc0fc0fff000qa69a69a69a69a69a69,mv9_mw3f03f00003f000000q28a28a28a28a28a28a,mv9_mwfc0fc003f000000000q30c30c30c30c30c30c,mv9_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im43q1 : (child43q1.toFinset.image (relWord p3)) = node20.toFinset := by
  simp only [child43q1,node20, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv3_mw3f000q208208208208208208,mv3_mw3ffffq618618618618618618,mv3_mw3ffc003fq924924924924924924,mv3_mw3ffc0000fc0q8a28a28a28a28a28a2,mv3_mwfc0fc0fc0000q249249249249249249,mv3_mwfff00000003f000q861861861861861861,mv3_mw3f03f00003f000000q28a28a28a28a28a28a,mv3_mwfc0fc003f000000000q30c30c30c30c30c30c,mv3_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im43q2 : (child43q2.toFinset.image (relWord p0)) = node23.toFinset := by
  simp only [child43q2,node23, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mwffffc0fc0ffffffqe79e79e79e79e79e79,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c,mv0_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im43q3 : (child43q3.toFinset.image (relWord p20)) = node35.toFinset := by
  simp only [child43q3,node35, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv20_mwfff00003ffff03fq965965965965965965,mv20_mw3ffffq618618618618618618,mv20_mw3ffc003fq924924924924924924,mv20_mw3ffc0000fc0q8a28a28a28a28a28a2,mv20_mwfc0fc0fc0000q249249249249249249,mv20_mwffffc0fc0fff000qa69a69a69a69a69a69,mv20_mw3f03f00003f000000q28a28a28a28a28a28a,mv20_mwfc0fc003f000000000q30c30c30c30c30c30c,mv20_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im43q4 : (child43q4.toFinset.image (relWord p14)) = node20.toFinset := by
  simp only [child43q4,node20, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv14_mwfc0000q820820820820820820,mv14_mw3ffffq618618618618618618,mv14_mw3ffc003fq924924924924924924,mv14_mw3ffc0000fc0q8a28a28a28a28a28a2,mv14_mwfc0fc0fc0000q249249249249249249,mv14_mwfff00000003f000q861861861861861861,mv14_mw3f03f00003f000000q28a28a28a28a28a28a,mv14_mwfc0fc003f000000000q30c30c30c30c30c30c,mv14_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im43q5 : (child43q5.toFinset.image (relWord p7)) = node23.toFinset := by
  simp only [child43q5,node23, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv7_mwffffc0ffffff03fqb6db6db6db6db6db6d,mv7_mw3ffffq618618618618618618,mv7_mw3ffc003fq924924924924924924,mv7_mw3ffc0000fc0q8a28a28a28a28a28a2,mv7_mwfc0fc0fc0000q249249249249249249,mv7_mwfff00000003f000q861861861861861861,mv7_mw3f03f00003f000000q28a28a28a28a28a28a,mv7_mwfc0fc003f000000000q30c30c30c30c30c30c,mv7_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im43q6 : (child43q6.toFinset.image (relWord p18)) = node35.toFinset := by
  simp only [child43q6,node35, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv18_mwfff03ffc003ffc0q8e38e38e38e38e38e3,mv18_mw3ffffq618618618618618618,mv18_mw3ffc003fq924924924924924924,mv18_mw3ffc0000fc0q8a28a28a28a28a28a2,mv18_mwfc0fc0fc0000q249249249249249249,mv18_mwffffc0fc0fff000qa69a69a69a69a69a69,mv18_mw3f03f00003f000000q28a28a28a28a28a28a,mv18_mwfc0fc003f000000000q30c30c30c30c30c30c,mv18_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im43q7 : (child43q7.toFinset.image (relWord p12)) = node20.toFinset := by
  simp only [child43q7,node20, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv12_mwfc0000000q820820820820820820,mv12_mw3ffffq618618618618618618,mv12_mw3ffc003fq924924924924924924,mv12_mw3ffc0000fc0q8a28a28a28a28a28a2,mv12_mwfc0fc0fc0000q249249249249249249,mv12_mwfff00000003f000q861861861861861861,mv12_mw3f03f00003f000000q28a28a28a28a28a28a,mv12_mwfc0fc003f000000000q30c30c30c30c30c30c,mv12_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im43q8 : (child43q8.toFinset.image (relWord p10)) = node23.toFinset := by
  simp only [child43q8,node23, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv10_mwfffffffc0ffffc0qaebaebaebaebaebaeb,mv10_mw3ffffq618618618618618618,mv10_mw3ffc003fq924924924924924924,mv10_mw3ffc0000fc0q8a28a28a28a28a28a2,mv10_mwfc0fc0fc0000q249249249249249249,mv10_mwfff00000003f000q861861861861861861,mv10_mw3f03f00003f000000q28a28a28a28a28a28a,mv10_mwfc0fc003f000000000q30c30c30c30c30c30c,mv10_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im43q9 : (child43q9.toFinset.image (relWord p13)) = node35.toFinset := by
  simp only [child43q9,node35, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv13_mw3f03ffc0ffffc0000q2cb2cb2cb2cb2cb2cb,mv13_mw3ffffq618618618618618618,mv13_mw3ffc003fq924924924924924924,mv13_mw3ffc0000fc0q8a28a28a28a28a28a2,mv13_mwfff00000003f000q861861861861861861,mv13_mwffffc0fc0fff000qa69a69a69a69a69a69,mv13_mw3f03f00003f000000q28a28a28a28a28a28a,mv13_mwfc0fc003f000000000q30c30c30c30c30c30c,mv13_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im43q10 : (child43q10.toFinset.image (relWord p16)) = node35.toFinset := by
  simp only [child43q10,node35, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv16_mwfc0fc0ffffc0fc0000q34d34d34d34d34d34d,mv16_mw3ffffq618618618618618618,mv16_mw3ffc003fq924924924924924924,mv16_mw3ffc0000fc0q8a28a28a28a28a28a2,mv16_mwfff00000003f000q861861861861861861,mv16_mwffffc0fc0fff000qa69a69a69a69a69a69,mv16_mw3f03f00003f000000q28a28a28a28a28a28a,mv16_mwfc0fc003f000000000q30c30c30c30c30c30c,mv16_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im43q11 : (child43q11.toFinset.image (relWord p39)) = node35.toFinset := by
  simp only [child43q11,node35, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv39_mwfffffffc000003f000qc71c71c71c71c71c71,mv39_mw3ffffq618618618618618618,mv39_mw3ffc003fq924924924924924924,mv39_mw3ffc0000fc0q8a28a28a28a28a28a2,mv39_mwfc0fc0fc0000q249249249249249249,mv39_mwffffc0fc0fff000qa69a69a69a69a69a69,mv39_mw3f03f00003f000000q28a28a28a28a28a28a,mv39_mwfc0fc003f000000000q30c30c30c30c30c30c,mv39_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im43q12 : (child43q12.toFinset.image (relWord p19)) = node20.toFinset := by
  simp only [child43q12,node20, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv19_mw3f000000000000q208208208208208208,mv19_mw3ffffq618618618618618618,mv19_mw3ffc003fq924924924924924924,mv19_mw3ffc0000fc0q8a28a28a28a28a28a2,mv19_mwfc0fc0fc0000q249249249249249249,mv19_mwfff00000003f000q861861861861861861,mv19_mw3f03f00003f000000q28a28a28a28a28a28a,mv19_mwfc0fc003f000000000q30c30c30c30c30c30c,mv19_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im43q13 : (child43q13.toFinset.image (relWord p35)) = node23.toFinset := by
  simp only [child43q13,node23, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv35_mw3fffffc0ffffff000qaebaebaebaebaebaeb,mv35_mw3ffffq618618618618618618,mv35_mw3ffc003fq924924924924924924,mv35_mw3ffc0000fc0q8a28a28a28a28a28a2,mv35_mwfc0fc0fc0000q249249249249249249,mv35_mwfff00000003f000q861861861861861861,mv35_mw3f03f00003f000000q28a28a28a28a28a28a,mv35_mwfc0fc003f000000000q30c30c30c30c30c30c,mv35_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im43q14 : (child43q14.toFinset.image (relWord p22)) = node20.toFinset := by
  simp only [child43q14,node20, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv22_mwfc0000000000000q208208208208208208,mv22_mw3ffffq618618618618618618,mv22_mw3ffc003fq924924924924924924,mv22_mw3ffc0000fc0q8a28a28a28a28a28a2,mv22_mwfc0fc0fc0000q249249249249249249,mv22_mwfff00000003f000q861861861861861861,mv22_mw3f03f00003f000000q28a28a28a28a28a28a,mv22_mwfc0fc003f000000000q30c30c30c30c30c30c,mv22_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im43q15 : (child43q15.toFinset.image (relWord p33)) = node23.toFinset := by
  simp only [child43q15,node23, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv33_mwfc0fffffffc0fff000qb6db6db6db6db6db6d,mv33_mw3ffffq618618618618618618,mv33_mw3ffc003fq924924924924924924,mv33_mw3ffc0000fc0q8a28a28a28a28a28a2,mv33_mwfc0fc0fc0000q249249249249249249,mv33_mwfff00000003f000q861861861861861861,mv33_mw3f03f00003f000000q28a28a28a28a28a28a,mv33_mwfc0fc003f000000000q30c30c30c30c30c30c,mv33_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im43q16 : (child43q16.toFinset.image (relWord p45)) = node20.toFinset := by
  simp only [child43q16,node20, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv45_mwfc0000000000q820820820820820820,mv45_mw3ffffq618618618618618618,mv45_mw3ffc003fq924924924924924924,mv45_mw3ffc0000fc0q8a28a28a28a28a28a2,mv45_mwfc0fc0fc0000q249249249249249249,mv45_mwfff00000003f000q861861861861861861,mv45_mw3f03f00003f000000q28a28a28a28a28a28a,mv45_mwfc0fc003f000000000q30c30c30c30c30c30c,mv45_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im43q17 : (child43q17.toFinset.image (relWord p42)) = node23.toFinset := by
  simp only [child43q17,node23, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv42_mwfffffffc0fc0fff000qe79e79e79e79e79e79,mv42_mw3ffffq618618618618618618,mv42_mw3ffc003fq924924924924924924,mv42_mw3ffc0000fc0q8a28a28a28a28a28a2,mv42_mwfc0fc0fc0000q249249249249249249,mv42_mwfff00000003f000q861861861861861861,mv42_mw3f03f00003f000000q28a28a28a28a28a28a,mv42_mwfc0fc003f000000000q30c30c30c30c30c30c,mv42_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
theorem excluded43 : ¬ Viable 9 node43 := by
  refine trace_close (r:=8) (xs:=node43) tab43 cert43 ?_ uniq43
  intro v hv
  simp only [tab43,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_viable_transport p9 sur9 im43q0 excluded35
  · exact not_viable_transport p3 sur3 im43q1 excluded20
  · exact not_viable_transport p0 sur0 im43q2 excluded23
  · exact not_viable_transport p20 sur20 im43q3 excluded35
  · exact not_viable_transport p14 sur14 im43q4 excluded20
  · exact not_viable_transport p7 sur7 im43q5 excluded23
  · exact not_viable_transport p18 sur18 im43q6 excluded35
  · exact not_viable_transport p12 sur12 im43q7 excluded20
  · exact not_viable_transport p10 sur10 im43q8 excluded23
  · exact not_viable_transport p13 sur13 im43q9 excluded35
  · exact not_viable_transport p16 sur16 im43q10 excluded35
  · exact not_viable_transport p39 sur39 im43q11 excluded35
  · exact not_viable_transport p19 sur19 im43q12 excluded20
  · exact not_viable_transport p35 sur35 im43q13 excluded23
  · exact not_viable_transport p22 sur22 im43q14 excluded20
  · exact not_viable_transport p33 sur33 im43q15 excluded23
  · exact not_viable_transport p45 sur45 im43q16 excluded20
  · exact not_viable_transport p42 sur42 im43q17 excluded23
private theorem im44q0 : (child44q0.toFinset.image (relWord p0)) = node16.toFinset := by
  simp only [child44q0,node16, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mw3fq0,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c,mv0_mwfff000fc0000000000qc30c30c30c30c30c30]
private theorem im44q1 : (child44q1.toFinset.image (relWord p0)) = node24.toFinset := by
  simp only [child44q1,node24, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mw3fffffffqf3cf3cf3cf3cf3cf3c,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c,mv0_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q2 : (child44q2.toFinset.image (relWord p2)) = node16.toFinset := by
  simp only [child44q2,node16, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2_mwfc0q0,mv2_mw3ffffq618618618618618618,mv2_mw3ffc003fq924924924924924924,mv2_mw3ffc0000fc0q8a28a28a28a28a28a2,mv2_mwfc0fc0fc0000q249249249249249249,mv2_mwfff00000003f000q861861861861861861,mv2_mw3f03f00003f000000q28a28a28a28a28a28a,mv2_mwfc0fc003f000000000q30c30c30c30c30c30c,mv2_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q3 : (child44q3.toFinset.image (relWord p2)) = node24.toFinset := by
  simp only [child44q3,node24, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2_mw3ffc003ffffqebaebaebaebaebaeba,mv2_mw3ffffq618618618618618618,mv2_mw3ffc003fq924924924924924924,mv2_mw3ffc0000fc0q8a28a28a28a28a28a2,mv2_mwfc0fc0fc0000q249249249249249249,mv2_mwfff00000003f000q861861861861861861,mv2_mw3f03f00003f000000q28a28a28a28a28a28a,mv2_mwfc0fc003f000000000q30c30c30c30c30c30c,mv2_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q4 : (child44q4.toFinset.image (relWord p0)) = node26.toFinset := by
  simp only [child44q4,node26, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mw0q208208208208208208,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c,mv0_mwfff000fc0000000000qc30c30c30c30c30c30]
private theorem im44q5 : (child44q5.toFinset.image (relWord p6)) = node40.toFinset := by
  simp only [child44q5,node40, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv6_mwfc0fc0ffffffq659659659659659659,mv6_mw3ffffq618618618618618618,mv6_mw3ffc003fq924924924924924924,mv6_mw3ffc0000fc0q8a28a28a28a28a28a2,mv6_mwfc0fc0fc0000q249249249249249249,mv6_mwfff00000003f000q861861861861861861,mv6_mw3f03f00003f000000q28a28a28a28a28a28a,mv6_mwfc0fc003f000000000q30c30c30c30c30c30c,mv6_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q6 : (child44q6.toFinset.image (relWord p3)) = node16.toFinset := by
  simp only [child44q6,node16, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv3_mw3f000q0,mv3_mw3ffffq618618618618618618,mv3_mw3ffc003fq924924924924924924,mv3_mw3ffc0000fc0q8a28a28a28a28a28a2,mv3_mwfc0fc0fc0000q249249249249249249,mv3_mwfff00000003f000q861861861861861861,mv3_mw3f03f00003f000000q28a28a28a28a28a28a,mv3_mwfc0fc003f000000000q30c30c30c30c30c30c,mv3_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q7 : (child44q7.toFinset.image (relWord p3)) = node24.toFinset := by
  simp only [child44q7,node24, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv3_mwfff00000003ffffqe79e79e79e79e79e79,mv3_mw3ffffq618618618618618618,mv3_mw3ffc003fq924924924924924924,mv3_mw3ffc0000fc0q8a28a28a28a28a28a2,mv3_mwfc0fc0fc0000q249249249249249249,mv3_mwfff00000003f000q861861861861861861,mv3_mw3f03f00003f000000q28a28a28a28a28a28a,mv3_mwfc0fc003f000000000q30c30c30c30c30c30c,mv3_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q8 : (child44q8.toFinset.image (relWord p7)) = node40.toFinset := by
  simp only [child44q8,node40, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv7_mw3f03f00003f03ffffq69a69a69a69a69a69a,mv7_mw3ffffq618618618618618618,mv7_mw3ffc003fq924924924924924924,mv7_mw3ffc0000fc0q8a28a28a28a28a28a2,mv7_mwfc0fc0fc0000q249249249249249249,mv7_mwfff00000003f000q861861861861861861,mv7_mw3f03f00003f000000q28a28a28a28a28a28a,mv7_mwfc0fc003f000000000q30c30c30c30c30c30c,mv7_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q9 : (child44q9.toFinset.image (relWord p10)) = node40.toFinset := by
  simp only [child44q9,node40, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv10_mwfc0fc003f00003ffffq71c71c71c71c71c71c,mv10_mw3ffffq618618618618618618,mv10_mw3ffc003fq924924924924924924,mv10_mw3ffc0000fc0q8a28a28a28a28a28a2,mv10_mwfc0fc0fc0000q249249249249249249,mv10_mwfff00000003f000q861861861861861861,mv10_mw3f03f00003f000000q28a28a28a28a28a28a,mv10_mwfc0fc003f000000000q30c30c30c30c30c30c,mv10_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q10 : (child44q10.toFinset.image (relWord p18)) = node42.toFinset := by
  simp only [child44q10,node42, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv18_mw0q410410410410410410,mv18_mw3ffffq618618618618618618,mv18_mw3ffc003fq924924924924924924,mv18_mw3ffc0000fc0q8a28a28a28a28a28a2,mv18_mwfc0fc0fc0000q249249249249249249,mv18_mwfff00000003f000q861861861861861861,mv18_mw3f03f00003f000000q28a28a28a28a28a28a,mv18_mwfc0fc003f000000000q30c30c30c30c30c30c,mv18_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q11 : (child44q11.toFinset.image (relWord p18)) = node43.toFinset := by
  simp only [child44q11,node43, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv18_mwfff000fc000003ffffqe38e38e38e38e38e38,mv18_mw3ffffq618618618618618618,mv18_mw3ffc003fq924924924924924924,mv18_mw3ffc0000fc0q8a28a28a28a28a28a2,mv18_mwfc0fc0fc0000q249249249249249249,mv18_mwfff00000003f000q861861861861861861,mv18_mw3f03f00003f000000q28a28a28a28a28a28a,mv18_mwfc0fc003f000000000q30c30c30c30c30c30c,mv18_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q12 : (child44q12.toFinset.image (relWord p6)) = node26.toFinset := by
  simp only [child44q12,node26, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv6_mw0q820820820820820820,mv6_mw3ffffq618618618618618618,mv6_mw3ffc003fq924924924924924924,mv6_mw3ffc0000fc0q8a28a28a28a28a28a2,mv6_mwfc0fc0fc0000q249249249249249249,mv6_mwfff00000003f000q861861861861861861,mv6_mw3f03f00003f000000q28a28a28a28a28a28a,mv6_mwfc0fc003f000000000q30c30c30c30c30c30c,mv6_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q13 : (child44q13.toFinset.image (relWord p0)) = node40.toFinset := by
  simp only [child44q13,node40, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mw3fffffc0fffq9a69a69a69a69a69a6,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c,mv0_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q14 : (child44q14.toFinset.image (relWord p14)) = node16.toFinset := by
  simp only [child44q14,node16, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv14_mwfc0000q0,mv14_mw3ffffq618618618618618618,mv14_mw3ffc003fq924924924924924924,mv14_mw3ffc0000fc0q8a28a28a28a28a28a2,mv14_mwfc0fc0fc0000q249249249249249249,mv14_mwfff00000003f000q861861861861861861,mv14_mw3f03f00003f000000q28a28a28a28a28a28a,mv14_mwfc0fc003f000000000q30c30c30c30c30c30c,mv14_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q15 : (child44q15.toFinset.image (relWord p14)) = node24.toFinset := by
  simp only [child44q15,node24, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv14_mwfc0ffffc003fqb6db6db6db6db6db6d,mv14_mw3ffffq618618618618618618,mv14_mw3ffc003fq924924924924924924,mv14_mw3ffc0000fc0q8a28a28a28a28a28a2,mv14_mwfc0fc0fc0000q249249249249249249,mv14_mwfff00000003f000q861861861861861861,mv14_mw3f03f00003f000000q28a28a28a28a28a28a,mv14_mwfc0fc003f000000000q30c30c30c30c30c30c,mv14_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q16 : (child44q16.toFinset.image (relWord p1)) = node40.toFinset := by
  simp only [child44q16,node40, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1_mwfff00003ffff03fq965965965965965965,mv1_mw3ffffq618618618618618618,mv1_mw3ffc003fq924924924924924924,mv1_mw3ffc0000fc0q8a28a28a28a28a28a2,mv1_mwfc0fc0fc0000q249249249249249249,mv1_mwfff00000003f000q861861861861861861,mv1_mw3f03f00003f000000q28a28a28a28a28a28a,mv1_mwfc0fc003f000000000q30c30c30c30c30c30c,mv1_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q17 : (child44q17.toFinset.image (relWord p15)) = node16.toFinset := by
  simp only [child44q17,node16, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv15_mw3f000000q0,mv15_mw3ffffq618618618618618618,mv15_mw3ffc003fq924924924924924924,mv15_mw3ffc0000fc0q8a28a28a28a28a28a2,mv15_mwfc0fc0fc0000q249249249249249249,mv15_mwfff00000003f000q861861861861861861,mv15_mw3f03f00003f000000q28a28a28a28a28a28a,mv15_mwfc0fc003f000000000q30c30c30c30c30c30c,mv15_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q18 : (child44q18.toFinset.image (relWord p15)) = node24.toFinset := by
  simp only [child44q18,node24, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv15_mw3f03f00003ffc003fqbaebaebaebaebaebae,mv15_mw3ffffq618618618618618618,mv15_mw3ffc003fq924924924924924924,mv15_mw3ffc0000fc0q8a28a28a28a28a28a2,mv15_mwfc0fc0fc0000q249249249249249249,mv15_mwfff00000003f000q861861861861861861,mv15_mw3f03f00003f000000q28a28a28a28a28a28a,mv15_mwfc0fc003f000000000q30c30c30c30c30c30c,mv15_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q19 : (child44q19.toFinset.image (relWord p4)) = node42.toFinset := by
  simp only [child44q19,node42, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv4_mw0q104104104104104104,mv4_mw3ffffq618618618618618618,mv4_mw3ffc003fq924924924924924924,mv4_mw3ffc0000fc0q8a28a28a28a28a28a2,mv4_mwfc0fc0fc0000q249249249249249249,mv4_mwfff00000003f000q861861861861861861,mv4_mw3f03f00003f000000q28a28a28a28a28a28a,mv4_mwfc0fc003f000000000q30c30c30c30c30c30c,mv4_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q20 : (child44q20.toFinset.image (relWord p4)) = node43.toFinset := by
  simp only [child44q20,node43, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv4_mwfc0fc003f03ffc003fqb2cb2cb2cb2cb2cb2c,mv4_mw3ffffq618618618618618618,mv4_mw3ffc003fq924924924924924924,mv4_mw3ffc0000fc0q8a28a28a28a28a28a2,mv4_mwfc0fc0fc0000q249249249249249249,mv4_mwfff00000003f000q861861861861861861,mv4_mw3f03f00003f000000q28a28a28a28a28a28a,mv4_mwfc0fc003f000000000q30c30c30c30c30c30c,mv4_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q21 : (child44q21.toFinset.image (relWord p34)) = node40.toFinset := by
  simp only [child44q21,node40, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv34_mwfff000fc003ffc003fqd34d34d34d34d34d34,mv34_mw3ffffq618618618618618618,mv34_mw3ffc003fq924924924924924924,mv34_mw3ffc0000fc0q8a28a28a28a28a28a2,mv34_mwfc0fc0fc0000q249249249249249249,mv34_mwfff00000003f000q861861861861861861,mv34_mw3f03f00003f000000q28a28a28a28a28a28a,mv34_mwfc0fc003f000000000q30c30c30c30c30c30c,mv34_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q22 : (child44q22.toFinset.image (relWord p12)) = node16.toFinset := by
  simp only [child44q22,node16, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv12_mwfc0000000q0,mv12_mw3ffffq618618618618618618,mv12_mw3ffc003fq924924924924924924,mv12_mw3ffc0000fc0q8a28a28a28a28a28a2,mv12_mwfc0fc0fc0000q249249249249249249,mv12_mwfff00000003f000q861861861861861861,mv12_mw3f03f00003f000000q28a28a28a28a28a28a,mv12_mwfc0fc003f000000000q30c30c30c30c30c30c,mv12_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q23 : (child44q23.toFinset.image (relWord p12)) = node24.toFinset := by
  simp only [child44q23,node24, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv12_mwffffc0fc0fc0qaebaebaebaebaebaeb,mv12_mw3ffffq618618618618618618,mv12_mw3ffc003fq924924924924924924,mv12_mw3ffc0000fc0q8a28a28a28a28a28a2,mv12_mwfc0fc0fc0000q249249249249249249,mv12_mwfff00000003f000q861861861861861861,mv12_mw3f03f00003f000000q28a28a28a28a28a28a,mv12_mwfc0fc003f000000000q30c30c30c30c30c30c,mv12_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q24 : (child44q24.toFinset.image (relWord p4)) = node40.toFinset := by
  simp only [child44q24,node40, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv4_mwfff03ffc003ffc0q8e38e38e38e38e38e3,mv4_mw3ffffq618618618618618618,mv4_mw3ffc003fq924924924924924924,mv4_mw3ffc0000fc0q8a28a28a28a28a28a2,mv4_mwfc0fc0fc0000q249249249249249249,mv4_mwfff00000003f000q861861861861861861,mv4_mw3f03f00003f000000q28a28a28a28a28a28a,mv4_mwfc0fc003f000000000q30c30c30c30c30c30c,mv4_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q25 : (child44q25.toFinset.image (relWord p1)) = node42.toFinset := by
  simp only [child44q25,node42, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1_mw0q82082082082082082,mv1_mw3ffffq618618618618618618,mv1_mw3ffc003fq924924924924924924,mv1_mw3ffc0000fc0q8a28a28a28a28a28a2,mv1_mwfc0fc0fc0000q249249249249249249,mv1_mwfff00000003f000q861861861861861861,mv1_mw3f03f00003f000000q28a28a28a28a28a28a,mv1_mwfc0fc003f000000000q30c30c30c30c30c30c,mv1_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q26 : (child44q26.toFinset.image (relWord p1)) = node43.toFinset := by
  simp only [child44q26,node43, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1_mw3f03f03ffff000fc0qaaaaaaaaaaaaaaaaaa,mv1_mw3ffffq618618618618618618,mv1_mw3ffc003fq924924924924924924,mv1_mw3ffc0000fc0q8a28a28a28a28a28a2,mv1_mwfc0fc0fc0000q249249249249249249,mv1_mwfff00000003f000q861861861861861861,mv1_mw3f03f00003f000000q28a28a28a28a28a28a,mv1_mwfc0fc003f000000000q30c30c30c30c30c30c,mv1_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q27 : (child44q27.toFinset.image (relWord p17)) = node16.toFinset := by
  simp only [child44q27,node16, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv17_mw3f000000000q0,mv17_mw3ffffq618618618618618618,mv17_mw3ffc003fq924924924924924924,mv17_mw3ffc0000fc0q8a28a28a28a28a28a2,mv17_mwfc0fc0fc0000q249249249249249249,mv17_mwfff00000003f000q861861861861861861,mv17_mw3f03f00003f000000q28a28a28a28a28a28a,mv17_mwfc0fc003f000000000q30c30c30c30c30c30c,mv17_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q28 : (child44q28.toFinset.image (relWord p17)) = node24.toFinset := by
  simp only [child44q28,node24, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv17_mwfc0fc003ffc0000fc0qbaebaebaebaebaebae,mv17_mw3ffffq618618618618618618,mv17_mw3ffc003fq924924924924924924,mv17_mw3ffc0000fc0q8a28a28a28a28a28a2,mv17_mwfc0fc0fc0000q249249249249249249,mv17_mwfff00000003f000q861861861861861861,mv17_mw3f03f00003f000000q28a28a28a28a28a28a,mv17_mwfc0fc003f000000000q30c30c30c30c30c30c,mv17_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q29 : (child44q29.toFinset.image (relWord p31)) = node40.toFinset := by
  simp only [child44q29,node40, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv31_mwfff000ffffc0000fc0qcb2cb2cb2cb2cb2cb2,mv31_mw3ffffq618618618618618618,mv31_mw3ffc003fq924924924924924924,mv31_mw3ffc0000fc0q8a28a28a28a28a28a2,mv31_mwfc0fc0fc0000q249249249249249249,mv31_mwfff00000003f000q861861861861861861,mv31_mw3f03f00003f000000q28a28a28a28a28a28a,mv31_mwfc0fc003f000000000q30c30c30c30c30c30c,mv31_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q30 : (child44q30.toFinset.image (relWord p0)) = node42.toFinset := by
  simp only [child44q30,node42, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mw0q41041041041041041,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c,mv0_mwfff000fc0000000000qc30c30c30c30c30c30]
private theorem im44q31 : (child44q31.toFinset.image (relWord p0)) = node43.toFinset := by
  simp only [child44q31,node43, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv0_mwffffc0fc0fff000qa69a69a69a69a69a69,mv0_mw3ffffq618618618618618618,mv0_mw3ffc003fq924924924924924924,mv0_mw3ffc0000fc0q8a28a28a28a28a28a2,mv0_mwfc0fc0fc0000q249249249249249249,mv0_mwfff00000003f000q861861861861861861,mv0_mw3f03f00003f000000q28a28a28a28a28a28a,mv0_mwfc0fc003f000000000q30c30c30c30c30c30c,mv0_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q32 : (child44q32.toFinset.image (relWord p28)) = node40.toFinset := by
  simp only [child44q32,node40, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv28_mw3f03ffc0ffffc0000q2cb2cb2cb2cb2cb2cb,mv28_mw3ffffq618618618618618618,mv28_mw3ffc003fq924924924924924924,mv28_mw3ffc0000fc0q8a28a28a28a28a28a2,mv28_mwfc0fc0fc0000q249249249249249249,mv28_mwfff00000003f000q861861861861861861,mv28_mw3f03f00003f000000q28a28a28a28a28a28a,mv28_mwfc0fc003f000000000q30c30c30c30c30c30c,mv28_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q33 : (child44q33.toFinset.image (relWord p25)) = node40.toFinset := by
  simp only [child44q33,node40, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv25_mwfc0fc0ffffc0fc0000q34d34d34d34d34d34d,mv25_mw3ffffq618618618618618618,mv25_mw3ffc003fq924924924924924924,mv25_mw3ffc0000fc0q8a28a28a28a28a28a2,mv25_mwfc0fc0fc0000q249249249249249249,mv25_mwfff00000003f000q861861861861861861,mv25_mw3f03f00003f000000q28a28a28a28a28a28a,mv25_mwfc0fc003f000000000q30c30c30c30c30c30c,mv25_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q34 : (child44q34.toFinset.image (relWord p39)) = node16.toFinset := by
  simp only [child44q34,node16, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv39_mwfc0000000000q0,mv39_mw3ffffq618618618618618618,mv39_mw3ffc003fq924924924924924924,mv39_mw3ffc0000fc0q8a28a28a28a28a28a2,mv39_mwfc0fc0fc0000q249249249249249249,mv39_mwfff00000003f000q861861861861861861,mv39_mw3f03f00003f000000q28a28a28a28a28a28a,mv39_mwfc0fc003f000000000q30c30c30c30c30c30c,mv39_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q35 : (child44q35.toFinset.image (relWord p39)) = node24.toFinset := by
  simp only [child44q35,node24, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv39_mwfff000fc0fc0fc0000qe79e79e79e79e79e79,mv39_mw3ffffq618618618618618618,mv39_mw3ffc003fq924924924924924924,mv39_mw3ffc0000fc0q8a28a28a28a28a28a2,mv39_mwfc0fc0fc0000q249249249249249249,mv39_mwfff00000003f000q861861861861861861,mv39_mw3f03f00003f000000q28a28a28a28a28a28a,mv39_mwfc0fc003f000000000q30c30c30c30c30c30c,mv39_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q36 : (child44q36.toFinset.image (relWord p13)) = node16.toFinset := by
  simp only [child44q36,node16, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv13_mw3f000000000000q0,mv13_mw3ffffq618618618618618618,mv13_mw3ffc003fq924924924924924924,mv13_mw3ffc0000fc0q8a28a28a28a28a28a2,mv13_mwfc0fc0fc0000q249249249249249249,mv13_mwfff00000003f000q861861861861861861,mv13_mw3f03f00003f000000q28a28a28a28a28a28a,mv13_mwfc0fc003f000000000q30c30c30c30c30c30c,mv13_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q37 : (child44q37.toFinset.image (relWord p13)) = node24.toFinset := by
  simp only [child44q37,node24, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv13_mw3ffff00003f03f000qaebaebaebaebaebaeb,mv13_mw3ffffq618618618618618618,mv13_mw3ffc003fq924924924924924924,mv13_mw3ffc0000fc0q8a28a28a28a28a28a2,mv13_mwfc0fc0fc0000q249249249249249249,mv13_mwfff00000003f000q861861861861861861,mv13_mw3f03f00003f000000q28a28a28a28a28a28a,mv13_mwfc0fc003f000000000q30c30c30c30c30c30c,mv13_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q38 : (child44q38.toFinset.image (relWord p16)) = node16.toFinset := by
  simp only [child44q38,node16, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv16_mwfc0000000000000q0,mv16_mw3ffffq618618618618618618,mv16_mw3ffc003fq924924924924924924,mv16_mw3ffc0000fc0q8a28a28a28a28a28a2,mv16_mwfc0fc0fc0000q249249249249249249,mv16_mwfff00000003f000q861861861861861861,mv16_mw3f03f00003f000000q28a28a28a28a28a28a,mv16_mwfc0fc003f000000000q30c30c30c30c30c30c,mv16_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q39 : (child44q39.toFinset.image (relWord p16)) = node24.toFinset := by
  simp only [child44q39,node24, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv16_mwfc0fff03f00003f000qb6db6db6db6db6db6d,mv16_mw3ffffq618618618618618618,mv16_mw3ffc003fq924924924924924924,mv16_mw3ffc0000fc0q8a28a28a28a28a28a2,mv16_mwfc0fc0fc0000q249249249249249249,mv16_mwfff00000003f000q861861861861861861,mv16_mw3f03f00003f000000q28a28a28a28a28a28a,mv16_mwfc0fc003f000000000q30c30c30c30c30c30c,mv16_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q40 : (child44q40.toFinset.image (relWord p30)) = node40.toFinset := by
  simp only [child44q40,node40, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv30_mwfffffffc000003f000qc71c71c71c71c71c71,mv30_mw3ffffq618618618618618618,mv30_mw3ffc003fq924924924924924924,mv30_mw3ffc0000fc0q8a28a28a28a28a28a2,mv30_mwfc0fc0fc0000q249249249249249249,mv30_mwfff00000003f000q861861861861861861,mv30_mw3f03f00003f000000q28a28a28a28a28a28a,mv30_mwfc0fc003f000000000q30c30c30c30c30c30c,mv30_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q41 : (child44q41.toFinset.image (relWord p24)) = node40.toFinset := by
  simp only [child44q41,node40, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv24_mwffffff03f03f000000q38e38e38e38e38e38e,mv24_mw3ffffq618618618618618618,mv24_mw3ffc003fq924924924924924924,mv24_mw3ffc0000fc0q8a28a28a28a28a28a2,mv24_mwfc0fc0fc0000q249249249249249249,mv24_mwfff00000003f000q861861861861861861,mv24_mw3f03f00003f000000q28a28a28a28a28a28a,mv24_mwfc0fc003f000000000q30c30c30c30c30c30c,mv24_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q42 : (child44q42.toFinset.image (relWord p38)) = node16.toFinset := by
  simp only [child44q42,node16, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv38_mw3f000000000000000q0,mv38_mw3ffffq618618618618618618,mv38_mw3ffc003fq924924924924924924,mv38_mw3ffc0000fc0q8a28a28a28a28a28a2,mv38_mwfc0fc0fc0000q249249249249249249,mv38_mwfff00000003f000q861861861861861861,mv38_mw3f03f00003f000000q28a28a28a28a28a28a,mv38_mwfc0fc003f000000000q30c30c30c30c30c30c,mv38_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q43 : (child44q43.toFinset.image (relWord p38)) = node24.toFinset := by
  simp only [child44q43,node24, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv38_mwfff03ffc003f000000qebaebaebaebaebaeba,mv38_mw3ffffq618618618618618618,mv38_mw3ffc003fq924924924924924924,mv38_mw3ffc0000fc0q8a28a28a28a28a28a2,mv38_mwfc0fc0fc0000q249249249249249249,mv38_mwfff00000003f000q861861861861861861,mv38_mw3f03f00003f000000q28a28a28a28a28a28a,mv38_mwfc0fc003f000000000q30c30c30c30c30c30c,mv38_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q44 : (child44q44.toFinset.image (relWord p36)) = node16.toFinset := by
  simp only [child44q44,node16, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv36_mwfc0000000000000000q0,mv36_mw3ffffq618618618618618618,mv36_mw3ffc003fq924924924924924924,mv36_mw3ffc0000fc0q8a28a28a28a28a28a2,mv36_mwfc0fc0fc0000q249249249249249249,mv36_mwfff00000003f000q861861861861861861,mv36_mw3f03f00003f000000q28a28a28a28a28a28a,mv36_mwfc0fc003f000000000q30c30c30c30c30c30c,mv36_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
private theorem im44q45 : (child44q45.toFinset.image (relWord p36)) = node24.toFinset := by
  simp only [child44q45,node24, List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv36_mwffffc0fff000000000qf3cf3cf3cf3cf3cf3c,mv36_mw3ffffq618618618618618618,mv36_mw3ffc003fq924924924924924924,mv36_mw3ffc0000fc0q8a28a28a28a28a28a2,mv36_mwfc0fc0fc0000q249249249249249249,mv36_mwfff00000003f000q861861861861861861,mv36_mw3f03f00003f000000q28a28a28a28a28a28a,mv36_mwfc0fc003f000000000q30c30c30c30c30c30c,mv36_mwfff000fc0000000000qc30c30c30c30c30c30]
  decide +kernel
theorem excluded44 : ¬ Viable 10 node44 := by
  refine trace_close (r:=9) (xs:=node44) tab44 cert44 ?_ uniq44
  intro v hv
  simp only [tab44,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_viable_transport p0 sur0 im44q0 excluded16
  · exact not_viable_transport p0 sur0 im44q1 excluded24
  · exact not_viable_transport p2 sur2 im44q2 excluded16
  · exact not_viable_transport p2 sur2 im44q3 excluded24
  · exact not_viable_transport p0 sur0 im44q4 excluded26
  · exact not_viable_transport p6 sur6 im44q5 excluded40
  · exact not_viable_transport p3 sur3 im44q6 excluded16
  · exact not_viable_transport p3 sur3 im44q7 excluded24
  · exact not_viable_transport p7 sur7 im44q8 excluded40
  · exact not_viable_transport p10 sur10 im44q9 excluded40
  · exact not_viable_transport p18 sur18 im44q10 excluded42
  · exact not_viable_transport p18 sur18 im44q11 excluded43
  · exact not_viable_transport p6 sur6 im44q12 excluded26
  · exact not_viable_transport p0 sur0 im44q13 excluded40
  · exact not_viable_transport p14 sur14 im44q14 excluded16
  · exact not_viable_transport p14 sur14 im44q15 excluded24
  · exact not_viable_transport p1 sur1 im44q16 excluded40
  · exact not_viable_transport p15 sur15 im44q17 excluded16
  · exact not_viable_transport p15 sur15 im44q18 excluded24
  · exact not_viable_transport p4 sur4 im44q19 excluded42
  · exact not_viable_transport p4 sur4 im44q20 excluded43
  · exact not_viable_transport p34 sur34 im44q21 excluded40
  · exact not_viable_transport p12 sur12 im44q22 excluded16
  · exact not_viable_transport p12 sur12 im44q23 excluded24
  · exact not_viable_transport p4 sur4 im44q24 excluded40
  · exact not_viable_transport p1 sur1 im44q25 excluded42
  · exact not_viable_transport p1 sur1 im44q26 excluded43
  · exact not_viable_transport p17 sur17 im44q27 excluded16
  · exact not_viable_transport p17 sur17 im44q28 excluded24
  · exact not_viable_transport p31 sur31 im44q29 excluded40
  · exact not_viable_transport p0 sur0 im44q30 excluded42
  · exact not_viable_transport p0 sur0 im44q31 excluded43
  · exact not_viable_transport p28 sur28 im44q32 excluded40
  · exact not_viable_transport p25 sur25 im44q33 excluded40
  · exact not_viable_transport p39 sur39 im44q34 excluded16
  · exact not_viable_transport p39 sur39 im44q35 excluded24
  · exact not_viable_transport p13 sur13 im44q36 excluded16
  · exact not_viable_transport p13 sur13 im44q37 excluded24
  · exact not_viable_transport p16 sur16 im44q38 excluded16
  · exact not_viable_transport p16 sur16 im44q39 excluded24
  · exact not_viable_transport p30 sur30 im44q40 excluded40
  · exact not_viable_transport p24 sur24 im44q41 excluded40
  · exact not_viable_transport p38 sur38 im44q42 excluded16
  · exact not_viable_transport p38 sur38 im44q43 excluded24
  · exact not_viable_transport p36 sur36 im44q44 excluded16
  · exact not_viable_transport p36 sur36 im44q45 excluded24
theorem no_cube617 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 6), (3, 7), (4, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, hm, hs, he⟩
  exact excluded44 (small_implies_viable hm hs he)
#print axioms no_cube617
end PEqualNP.Outside.Meta617
