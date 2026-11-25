import PEqualNP.Defs

/-!
# Counting the frontier of a cut in a binary circuit

Wire indices are absolute. Primary wires are below the first gate's index.
Put the gate outputs at which the traversal should stop in `marked`. The
frontier contains the distinct wires still demanded after scanning all gates
backwards. The expanded set contains exactly the unmarked outputs actually
replaced by their operands. Both sets discard duplicates from shared paths.

The counting argument uses only the fan-in bound. It applies to arbitrary
operations and any number of requested output wires.
-/

open PEqualNP.CircuitLowerBounds

namespace CircuitCutFrontier

structure Trace where
  frontier : Finset ℕ
  expanded : Finset ℕ

/-- Scan the suffix first, then inspect its demand for the current gate output. -/
def trace (marked : Finset ℕ) : List Gate → ℕ → Finset ℕ → Trace
  | [], _, out => ⟨out, ∅⟩
  | g :: gs, m, out =>
    let t := trace marked gs (m + 1) out
    if m ∈ t.frontier ∧ m ∉ marked then
      ⟨t.frontier.erase m ∪ g.inputs.toFinset, insert m t.expanded⟩
    else t

/-- Every expanded wire is an unmarked gate output in the scanned interval. -/
theorem expanded_mem {marked out : Finset ℕ} {gs : List Gate} {m w : ℕ}
    (h : w ∈ (trace marked gs m out).expanded) :
    m ≤ w ∧ w < m + gs.length ∧ w ∉ marked := by
  induction gs generalizing m with
  | nil => simp [trace] at h
  | cons g gs ih =>
    simp only [trace] at h
    split at h
    next take =>
      rcases Finset.mem_insert.mp h with rfl | ht
      · exact ⟨le_rfl, by simp, take.2⟩
      · obtain ⟨lo, hi, unmarked⟩ := ih ht
        exact ⟨by omega, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi, unmarked⟩
    next =>
      obtain ⟨lo, hi, unmarked⟩ := ih h
      exact ⟨by omega, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi, unmarked⟩

/-- One binary expansion increases the number of distinct demanded wires by at most one. -/
theorem frontier_card_le (marked out : Finset ℕ) (gs : List Gate) (m : ℕ)
    (fan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (trace marked gs m out).frontier.card ≤ out.card + (trace marked gs m out).expanded.card := by
  induction gs generalizing m with
  | nil => simp [trace]
  | cons g gs ih =>
    let t := trace marked gs (m + 1) out
    have htail : t.frontier.card ≤ out.card + t.expanded.card :=
      ih (m + 1) (fun z hz => fan z (by simp [hz]))
    have hfresh : m ∉ t.expanded := by
      intro hm
      have lo := (expanded_mem hm).1
      omega
    change (if m ∈ t.frontier ∧ m ∉ marked then
      (⟨t.frontier.erase m ∪ g.inputs.toFinset, insert m t.expanded⟩ : Trace)
      else t).frontier.card ≤ out.card + (if m ∈ t.frontier ∧ m ∉ marked then
      (⟨t.frontier.erase m ∪ g.inputs.toFinset, insert m t.expanded⟩ : Trace)
      else t).expanded.card
    split
    next take =>
      simp only [Finset.card_insert_of_notMem hfresh]
      have small := (List.toFinset_card_le g.inputs).trans (fan g (by simp))
      have union := Finset.card_union_le (t.frontier.erase m) g.inputs.toFinset
      have erased := Finset.card_erase_add_one take.1
      omega
    next => exact htail

/-- Backwards cut from the circuit's designated output wire. -/
def outputTrace (n : ℕ) (C : Circuit) (marked : Finset ℕ) : Trace :=
  trace marked C.gates n {C.output}

/-- At a single output, the distinct frontier wires number at most one plus the
distinct expanded gates. Mark all pure outputs to count expansions of mixed gates. -/
theorem output_frontier_card_le (n : ℕ) (C : Circuit) (marked : Finset ℕ)
    (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (outputTrace n C marked).frontier.card ≤ 1 + (outputTrace n C marked).expanded.card := by
  simpa [outputTrace] using frontier_card_le marked {C.output} C.gates n fan

/-- The expanded set is contained in all nonmarked gate outputs, including
outputs of gates that the designated output does not depend on. -/
theorem expanded_subset_unmarked (n : ℕ) (C : Circuit) (marked : Finset ℕ) :
    (outputTrace n C marked).expanded ⊆ Finset.Ico n (n + C.size) \ marked := by
  intro w hw
  obtain ⟨lo, hi, unmarked⟩ := expanded_mem (gs := C.gates) hw
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_Ico.mpr ⟨lo, hi⟩, unmarked⟩

/-- The same bound using all unmarked gate outputs. -/
theorem output_frontier_card_le_unmarked (n : ℕ) (C : Circuit) (marked : Finset ℕ)
    (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (outputTrace n C marked).frontier.card ≤ 1 + (Finset.Ico n (n + C.size) \ marked).card :=
  (output_frontier_card_le n C marked fan).trans
    (Nat.add_le_add_left (Finset.card_le_card (expanded_subset_unmarked n C marked)) 1)

end CircuitCutFrontier

#print axioms CircuitCutFrontier.expanded_mem
#print axioms CircuitCutFrontier.output_frontier_card_le
#print axioms CircuitCutFrontier.output_frontier_card_le_unmarked
