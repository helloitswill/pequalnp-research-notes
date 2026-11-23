import PEqualNP.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

namespace PEqualNP.Outside.Net662

def net : SimpleGraph (Fin 6) where
  Adj i j := (i.val < 3 ∧ j.val < 3 ∧ i ≠ j) ∨ i.val + j.val = 5
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

private def netAdjDec : DecidableRel net.Adj :=
  fun i j => inferInstanceAs (Decidable ((i.val < 3 ∧ j.val < 3 ∧ i ≠ j) ∨ i.val + j.val = 5))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma noSquare : ∀ a b c e, net.Adj a b → net.Adj b c → net.Adj c e →
    net.Adj e a → a = c ∨ b = e := by
  letI : DecidableRel net.Adj := netAdjDec
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma coverLower : ∀ T : Finset (Fin 6),
    (∀ i j : Fin 6, net.Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  letI : DecidableRel net.Adj := netAdjDec
  decide

def netEdges : Finset (Sym2 (Fin 6)) :=
  {s(0, 1), s(0, 2), s(1, 2), s(0, 5), s(1, 4), s(2, 3)}

lemma adjEdges : ∀ a b : Fin 6, net.Adj a b ↔ s(a, b) ∈ netEdges := by
  letI : DecidableRel net.Adj := netAdjDec
  decide

lemma edgeCount : net.edgeSet.ncard = 6 := by
  have he : net.edgeSet = (netEdges : Set (Sym2 (Fin 6))) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ a b => exact adjEdges a b
  rw [he, Set.ncard_coe_finset]
  decide

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circuit : Circuit :=
  ⟨[⟨.or,[0,1]⟩,⟨.and,[2,3]⟩,⟨.or,[4,0]⟩,⟨.or,[5,1]⟩,
    ⟨.or,[6,7]⟩,⟨.or,[2,8]⟩,⟨.or,[9,2]⟩,⟨.and,[10,11]⟩,⟨.and,[12,13]⟩],14⟩

private def andSet : Finset ℕ := {1,7,8}
private def wideSet : Finset ℕ := {0,2,3,4,5,6}

private lemma monotone : Monotone2 circuit := by
  intro g hg
  simp [circuit] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]

private lemma vectorForm (x : Fin 6 → Bool) :
    x = ![x 0,x 1,x 2,x 3,x 4,x 5] := by
  funext i
  fin_cases i <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private lemma evaluates (x : Fin 6 → Bool) :
    circuit.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6,
      ((u.val < 3 ∧ v.val < 3 ∧ u ≠ v) ∨ u.val + v.val = 5) ∧ x u = true ∧ x v = true := by
  have h : ∀ a b c d e f : Bool,
      circuit.eval (List.ofFn ![a,b,c,d,e,f]) = true ↔ ∃ u v : Fin 6,
        ((u.val < 3 ∧ v.val < 3 ∧ u ≠ v) ∨ u.val + v.val = 5) ∧
          ![a,b,c,d,e,f] u = true ∧ ![a,b,c,d,e,f] v = true := by decide
  simpa only [← vectorForm x] using h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

private lemma gateIndex {j : ℕ} {g : Gate} (he : circuit.gates[j]? = some g) : j < 9 := by
  by_contra! hj
  have hn := List.getElem?_eq_none (l := circuit.gates) (i := j) (by exact hj)
  simp_all

private lemma andIndex (j : ℕ) (g : Gate) (he : circuit.gates[j]? = some g)
    (ha : g.op = GateOp.and) : j ∈ andSet := by
  have hj := gateIndex he
  interval_cases j <;> simp [circuit] at he <;> subst g <;> first | contradiction | decide

private lemma orIndex (j : ℕ) (g : Gate) (he : circuit.gates[j]? = some g)
    (ho : g.op = GateOp.or) : j ∈ wideSet := by
  have hj := gateIndex he
  interval_cases j <;> simp [circuit] at he <;> subst g <;> first | contradiction | decide

set_option maxRecDepth 4096 in
private lemma orWide (j : ℕ) (g : Gate) (he : circuit.gates[j]? = some g)
    (ho : g.op = GateOp.or) : ∃ u v : Fin 6, u ≠ v ∧
        (circuit.wires (List.ofFn (fun i : Fin 6 => decide (i = u)))).getD (6 + j) false = true ∧
        (circuit.wires (List.ofFn (fun i : Fin 6 => decide (i = v)))).getD (6 + j) false = true := by
  have hj := gateIndex he
  interval_cases j <;> simp [circuit] at he <;> subst g <;> first | contradiction | decide

private lemma counts : andSet.card = 3 ∧ wideSet.card = 6 := by decide

end PEqualNP.Outside.Net662

namespace PEqualNP.Outside

open Net662

theorem L_meta_662 : ¬ (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A B D : Finset ℕ), (∀ a b c e : Fin n, G.Adj a b → G.Adj b c → G.Adj c e → G.Adj e a → a = c ∨ b = e) → (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → (∃ u v : Fin n, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD (n + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD (n + j) false = true) → j ∈ B) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ¬ (∃ u v : Fin n, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD (n + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD (n + j) false = true) → j ∈ D) → G.edgeSet.ncard + 2 * k ≤ A.card + B.card + 2 * D.card + 2) := by
  intro bound
  have h := bound 6 3 net circuit andSet wideSet ∅ noSquare coverLower monotone evaluates
    andIndex (fun j g he ho _ => orIndex j g he ho)
    (fun j g he ho hn => (hn (orWide j g he ho)).elim)
  rw [edgeCount, counts.1, counts.2, Finset.card_empty] at h
  omega

end PEqualNP.Outside
