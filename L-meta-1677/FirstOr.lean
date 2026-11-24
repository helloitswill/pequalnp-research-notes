import Std

namespace FirstOr

-- The argument works for every deterministic operation on the selected wires.
structure Gate where
  inputs : List Nat
  operation : List Bool → Bool

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.operation (g.inputs.map fun i => w.getD i false)]

def AgreeExcept (v : Nat) (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, i ≠ v → x.getD i false = y.getD i false

theorem append_same {v : Nat} {x y : List Bool} (h : AgreeExcept v x y) (b : Bool) :
    AgreeExcept v (x ++ [b]) (y ++ [b]) := by
  obtain ⟨hlen, hw⟩ := h
  refine ⟨by simp [hlen], ?_⟩
  intro i hi
  simp only [List.getD_eq_getElem?_getD]
  by_cases hl : i < x.length
  · have hr : i < y.length := hlen ▸ hl
    rw [List.getElem?_append_left hl, List.getElem?_append_left hr]
    exact hw i hi
  · have hx : x.length ≤ i := by omega
    have hy : y.length ≤ i := by omega
    rw [List.getElem?_append_right hx, List.getElem?_append_right hy, hlen]

theorem tail_agrees (v : Nat) (gates : List Gate) {xs ys : List Bool}
    (h : AgreeExcept v xs ys) (skip : ∀ g ∈ gates, v ∉ g.inputs) :
    AgreeExcept v (gates.foldl step xs) (gates.foldl step ys) := by
  induction gates generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    have port : ∀ i ∈ g.inputs, xs.getD i false = ys.getD i false := by
      intro i hi
      exact h.2 i (fun e => skip g (by simp) (e ▸ hi))
    have hm : g.inputs.map (fun i => xs.getD i false) =
        g.inputs.map (fun i => ys.getD i false) := List.map_congr_left port
    apply ih
    · unfold step
      rw [hm]
      exact append_same h _
    · intro gate hv
      exact skip gate (by simp [hv])

def selected (mask : Nat) : List Bool := (List.range 9).map (fun i => mask.testBit i)

def initial (mask : Nat) : List Bool :=
  (selected mask) ++ [mask.testBit 0 || mask.testBit 6]

def graph (x : Nat) : Bool :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)].any
    (fun (a,b) => x.testBit a && x.testBit b)

private theorem outside {v : Nat} {a b : List Bool} (ha : a.length = 10)
    (hb : b.length = 10) (h : ∀ i : Fin 10, i.val ≠ v → a.getD i.val false = b.getD i.val false) :
    AgreeExcept v a b := by
  refine ⟨ha.trans hb.symm, ?_⟩
  intro i hi
  by_cases hlt : i < 10
  · exact h ⟨i, hlt⟩ hi
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega : a.length ≤ i),
        List.getElem?_eq_none (by omega : b.length ≤ i)]

theorem must_read (v lo hi : Nat) (gates : List Gate) (out : Nat)
    (hrows : AgreeExcept v (initial lo) (initial hi)) (hdiff : graph lo ≠ graph hi)
    (hout : out ≠ v) (correct : ∀ m, (gates.foldl step (initial m)).getD out false = graph m) :
    ∃ g ∈ gates, v ∈ g.inputs := by
  apply Classical.byContradiction
  intro hn
  have hs : ∀ g ∈ gates, v ∉ g.inputs := fun g hg hv => hn ⟨g,hg,hv⟩
  have equal := (tail_agrees v gates hrows hs).2 out hout
  rw [correct lo, correct hi] at equal
  exact hdiff equal

theorem both_inputs_needed (gates : List Gate) (out : Nat) (hout : 9 ≤ out)
    (correct : ∀ m, (gates.foldl step (initial m)).getD out false = graph m) :
    (∃ g ∈ gates, 0 ∈ g.inputs) ∧ (∃ g ∈ gates, 6 ∈ g.inputs) := by
  constructor
  · apply must_read 0 80 81 gates out (outside (by decide) (by decide) (by decide))
      (by decide) (by omega) correct
  · apply must_read 6 257 321 gates out (outside (by decide) (by decide) (by decide))
      (by decide) (by omega) correct

end FirstOr
