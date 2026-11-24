import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1677_1
    (hpos : ∀ D : Circuit, FanInTwo D → (∀ g ∈ D.gates, g.op ≠ GateOp.not) →
      D.size ≤ 14 → ∃ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 0 || x 6]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (hneg : ∀ D : Circuit, FanInTwo D → (∃ g ∈ D.gates, g.op = GateOp.not) →
      D.size ≤ 14 → ∃ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 0 || x 6]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C hfan hfirst hfun
  cases C with
  | mk gates out =>
    cases gates with
    | nil =>
      have impossible := hfirst (fun _ => true)
      change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at impossible
      simp [List.getD_eq_getElem?_getD] at impossible
    | cons g gs =>
      apply Classical.byContradiction
      intro hsize
      let D : Circuit := ⟨gs, out⟩
      have hD : FanInTwo D := by
        intro k hk
        exact hfan k (List.mem_cons_of_mem _ hk)
      have small : D.size ≤ 14 := by
        change ¬ 16 ≤ (g :: gs).length at hsize
        change gs.length ≤ 14
        simp only [List.length_cons] at hsize
        omega
      let step := fun (w : List Bool) (k : Gate) =>
        w ++ [k.op.eval (k.inputs.map fun i => w.getD i false)]
      have keeps : ∀ (tail : List Gate) (w : List Bool) (i : Nat), i < w.length →
          (tail.foldl step w).getD i false = w.getD i false := by
        intro tail
        induction tail with
        | nil => intro w i hi; rfl
        | cons k ks ih =>
          intro w i hi
          change (ks.foldl step (step w k)).getD i false = w.getD i false
          rw [ih (step w k) i (by simp [step]; omega)]
          simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      have first (x : Fin 9 → Bool) :
          g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 6) := by
        have hw := hfirst x
        change (gs.foldl step (step (List.ofFn x) g)).getD 9 false = _ at hw
        rw [keeps gs _ 9 (by simp [step])] at hw
        simpa [step, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by simp : (List.ofFn x).length ≤ 9)] using hw
      have agrees (x : Fin 9 → Bool) :
          D.eval (List.ofFn x ++ [x 0 || x 6]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
        have hx := congrFun hfun x
        change (gs.foldl step (step (List.ofFn x) g)).getD out false = _ at hx
        change (gs.foldl step (List.ofFn x ++ [x 0 || x 6])).getD out false = _
        simpa only [step, first x] using hx
      by_cases anyNot : ∃ k ∈ D.gates, k.op = GateOp.not
      · obtain ⟨x, bad⟩ := hneg D hD anyNot small
        exact bad (agrees x)
      · have none : ∀ k ∈ D.gates, k.op ≠ GateOp.not := fun k hk he => anyNot ⟨k,hk,he⟩
        obtain ⟨x, bad⟩ := hpos D hD none small
        exact bad (agrees x)
