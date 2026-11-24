import Std

namespace GateBudget

-- A wire's flag records whether a primary input can reach it through OR gates alone.
structure Port where
  index : Nat
  linear : Bool
  deriving DecidableEq

inductive Op where
  | meet | join
  deriving DecidableEq

structure Gate where
  index : Nat
  op : Op
  left : Port
  right : Port

def Gate.output (g : Gate) : Port :=
  ⟨g.index, (g.op == .join) && (g.left.linear || g.right.linear)⟩

-- Only wires with no OR-only path to a primary input draw on the budget.
def weight (p : Port) : Nat := if p.linear then 0 else 1

def pending : List Port → Nat
  | [] => 0
  | p :: ps => weight p + pending ps

def request (p : Port) (ps : List Port) : List Port :=
  if p ∈ ps then ps else p :: ps

theorem pending_request (p : Port) (ps : List Port) :
    pending (request p ps) ≤ pending ps + weight p := by
  unfold request
  split <;> simp [pending] <;> omega

theorem pending_erase (p : Port) (ps : List Port) (h : p ∈ ps) :
    pending (ps.erase p) + weight p = pending ps := by
  induction ps with
  | nil => simp at h
  | cons q qs ih =>
    by_cases heq : q = p
    · subst q
      simp [pending, Nat.add_comm]
    · have hmem : p ∈ qs := (List.mem_cons.mp h).resolve_left (Ne.symm heq)
      rw [List.erase_cons_tail (by simpa using heq)]
      simp only [pending]
      have := ih hmem
      omega

structure Count where
  products : Nat
  others : Nat
  deriving Repr

def Gate.count (g : Gate) (c : Count) : Count :=
  if g.left.linear && g.right.linear then
    match g.op with
    | .meet => { c with products := c.products + 1 }
    | .join => c
  else { c with others := c.others + 1 }

-- Gates are scanned in reverse execution order. Each live output is visited once,
-- even if several consumers requested it. Unused gates contribute to neither count.
def count : List Gate → List Port → Count
  | [], _ => ⟨0, 0⟩
  | g :: gs, ps =>
    if g.output ∈ ps then
      let rest := ps.erase g.output
      g.count (count gs (request g.left (request g.right rest)))
    else count gs ps

theorem gate_budget (gs : List Gate) (ps : List Port) :
    (count gs ps).products ≤ (count gs ps).others + pending ps := by
  induction gs generalizing ps with
  | nil => simp [count]
  | cons g gs ih =>
    by_cases h : g.output ∈ ps
    · simp only [count, ite_eq_left h]
      let rest := ps.erase g.output
      let next := request g.left (request g.right rest)
      have hdrop : pending rest + weight g.output = pending ps := pending_erase _ _ h
      have hr := pending_request g.right rest
      have hl : pending next ≤ pending (request g.right rest) + weight g.left :=
        pending_request g.left _
      have hi := ih next
      change (g.count (count gs next)).products ≤ (g.count (count gs next)).others + pending ps
      cases hop : g.op <;> cases ha : g.left.linear <;> cases hb : g.right.linear <;>
        simp [Gate.count, Gate.output, weight, hop, ha, hb] at hdrop hr hl ⊢ <;> omega
    · simpa only [count, ite_eq_right h] using ih ps

theorem one_output (gs : List Gate) (out : Port) :
    (count gs [out]).products ≤ (count gs [out]).others + 1 := by
  have h := gate_budget gs [out]
  have hp : pending [out] ≤ 1 := by cases hv : out.linear <;> simp [pending, weight, hv]
  omega

-- The usual C4-free common-neighbor criterion turns each legal product into a star.
theorem star_or_star {V : Type} {adj : V → V → Prop}
    (noSquare : ∀ a b c d, a ≠ b → c ≠ d →
      adj a c → adj a d → adj b c → adj b d → False)
    (left right : V → Prop) (safe : ∀ a b, left a → right b → adj a b) :
    (∀ a b, left a → left b → a = b) ∨ (∀ c d, right c → right d → c = d) := by
  classical
  by_cases h : ∀ a b, left a → left b → a = b
  · exact Or.inl h
  · apply Or.inr
    intro c d hc hd
    apply Classical.byContradiction
    intro hcd
    apply h
    intro a b ha hb
    apply Classical.byContradiction
    intro hab
    exact noSquare a b c d hab hcd (safe a c ha hc) (safe a d ha hd)
      (safe b c hb hc) (safe b d hb hd)

-- Apply this scan to the union DAG for neighbor sets, tagging each wire by its
-- center. Contract wires with just one primary source to that source first.
structure UnionGate (α : Type) where
  output : α
  left : α
  right : α

structure UnionResult (α : Type) where
  terminals : List α
  joins : Nat

def addRequest {α : Type} [DecidableEq α] (a : α) (as : List α) : List α :=
  if a ∈ as then as else a :: as

theorem length_addRequest {α : Type} [DecidableEq α] (a : α) (as : List α) :
    (addRequest a as).length ≤ as.length + 1 := by
  unfold addRequest
  split <;> simp

def unionScan {α : Type} [DecidableEq α] :
    List (UnionGate α) → List α → UnionResult α
  | [], ps => ⟨ps, 0⟩
  | g :: gs, ps =>
    if g.output ∈ ps then
      let next := addRequest g.left (addRequest g.right (ps.erase g.output))
      let r := unionScan gs next
      { r with joins := r.joins + 1 }
    else unionScan gs ps

theorem union_budget {α : Type} [DecidableEq α] (gs : List (UnionGate α)) (ps : List α) :
    (unionScan gs ps).terminals.length ≤ ps.length + (unionScan gs ps).joins := by
  induction gs generalizing ps with
  | nil => simp [unionScan]
  | cons g gs ih =>
    by_cases h : g.output ∈ ps
    · simp only [unionScan, ite_eq_left h]
      let rest := ps.erase g.output
      let next := addRequest g.left (addRequest g.right rest)
      have hr := length_addRequest g.right rest
      have hl : next.length ≤ (addRequest g.right rest).length + 1 := length_addRequest _ _
      have he : rest.length = ps.length - 1 := List.length_erase_of_mem h
      have hp : 0 < ps.length := List.length_pos_of_mem h
      have hi := ih next
      change (unionScan gs next).terminals.length ≤ ps.length + ((unionScan gs next).joins + 1)
      omega
    · simpa only [unionScan, ite_eq_right h] using ih ps

-- Distinct centers cannot both use a neighbor-arm wire carrying two distinct inputs.
theorem unique_center {V : Type} {adj : V → V → Prop}
    (noSquare : ∀ a b c d, a ≠ b → c ≠ d →
      adj a c → adj a d → adj b c → adj b d → False)
    {a b c d : V} (hcd : c ≠ d)
    (hac : adj a c) (had : adj a d) (hbc : adj b c) (hbd : adj b d) : a = b := by
  exact Classical.byContradiction (fun hab => noSquare a b c d hab hcd hac had hbc hbd)

theorem covered_edge_budget (edges selected products bottom others size : Nat)
    (terminals : edges ≤ bottom + selected) (connect : products ≤ others + 1)
    (partition : bottom + products + others ≤ size) :
    edges + 2 * products ≤ size + selected + 1 := by omega

theorem covered_graph_bound (edges cover selected products bottom others size : Nat)
    (terminals : edges ≤ bottom + selected) (connect : products ≤ others + 1)
    (partition : bottom + products + others ≤ size)
    (centers : cover ≤ selected) (selection : selected ≤ products) :
    edges + cover ≤ size + 1 := by omega

-- Two equal-size circuits for a gadget found by the finite search.
-- This identity also holds when the five signals have dependencies or fanout.
theorem bull_rewrite (a b c d e : Bool) :
    ((a || b) && (e || ((a || c) && (b || d)))) =
    ((a && ((b || d) || e)) || (b && (c || e))) := by
  cases a <;> cases b <;> simp [Bool.or_comm]

-- In the mixed two-AND circuit, C triggers the OR arm, X and Y each also
-- trigger one inner arm, and Z triggers only the outer conjunct.
theorem two_meet_expansion (c x y z p q : Bool) :
    ((x || y || z) && (c || ((x || p) && (y || q)))) =
    ((c && x) || (c && y) || (c && z) || (x && y) ||
     (x && q) || (y && p) || (z && p && q)) := by
  cases c <;> cases x <;> cases y <;> cases z <;> cases p <;> cases q <;> rfl

end GateBudget
