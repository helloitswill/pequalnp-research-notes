import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
namespace PlaneDoubleRead

-- Lines in PG(2,3) are the translates of {0, 1, 3, 9}. The first 39 gates
-- form the point disjunctions for the 13 lines. Let A be the term for line
-- zero, P the point disjunction for line one, and L the line-one input.
-- Gates 40 to 42 replace A OR (L AND P) by (A OR P) AND (A OR L).
-- On the incidence of point zero with line zero, both factors must read A.

def circuit : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.or, [3, 9]⟩,
  ⟨.or, [26, 27]⟩,
  ⟨.or, [1, 2]⟩,
  ⟨.or, [4, 10]⟩,
  ⟨.or, [29, 30]⟩,
  ⟨.or, [2, 3]⟩,
  ⟨.or, [5, 11]⟩,
  ⟨.or, [32, 33]⟩,
  ⟨.or, [3, 4]⟩,
  ⟨.or, [6, 12]⟩,
  ⟨.or, [35, 36]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.or, [7, 0]⟩,
  ⟨.or, [38, 39]⟩,
  ⟨.or, [5, 6]⟩,
  ⟨.or, [8, 1]⟩,
  ⟨.or, [41, 42]⟩,
  ⟨.or, [6, 7]⟩,
  ⟨.or, [9, 2]⟩,
  ⟨.or, [44, 45]⟩,
  ⟨.or, [7, 8]⟩,
  ⟨.or, [10, 3]⟩,
  ⟨.or, [47, 48]⟩,
  ⟨.or, [8, 9]⟩,
  ⟨.or, [11, 4]⟩,
  ⟨.or, [50, 51]⟩,
  ⟨.or, [9, 10]⟩,
  ⟨.or, [12, 5]⟩,
  ⟨.or, [53, 54]⟩,
  ⟨.or, [10, 11]⟩,
  ⟨.or, [0, 6]⟩,
  ⟨.or, [56, 57]⟩,
  ⟨.or, [11, 12]⟩,
  ⟨.or, [1, 7]⟩,
  ⟨.or, [59, 60]⟩,
  ⟨.or, [12, 0]⟩,
  ⟨.or, [2, 8]⟩,
  ⟨.or, [62, 63]⟩,
  ⟨.and, [13, 28]⟩,
  ⟨.or, [65, 31]⟩,
  ⟨.or, [65, 14]⟩,
  ⟨.and, [66, 67]⟩,
  ⟨.and, [15, 34]⟩,
  ⟨.and, [16, 37]⟩,
  ⟨.and, [17, 40]⟩,
  ⟨.and, [18, 43]⟩,
  ⟨.and, [19, 46]⟩,
  ⟨.and, [20, 49]⟩,
  ⟨.and, [21, 52]⟩,
  ⟨.and, [22, 55]⟩,
  ⟨.and, [23, 58]⟩,
  ⟨.and, [24, 61]⟩,
  ⟨.and, [25, 64]⟩,
  ⟨.or, [68, 69]⟩,
  ⟨.or, [80, 70]⟩,
  ⟨.or, [81, 71]⟩,
  ⟨.or, [82, 72]⟩,
  ⟨.or, [83, 73]⟩,
  ⟨.or, [84, 74]⟩,
  ⟨.or, [85, 75]⟩,
  ⟨.or, [86, 76]⟩,
  ⟨.or, [87, 77]⟩,
  ⟨.or, [88, 78]⟩,
  ⟨.or, [89, 79]⟩], 90⟩

def v (i : ℕ) : Bool := decide (i ∈ ([13, 65, 66, 67] : List ℕ))

def vBase : List Bool := [true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

def w (i : ℕ) : Bool := decide (i ∈ ([0, 26, 28, 39, 40, 57, 58, 62, 64, 65, 66, 67] : List ℕ))

def wBase : List Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

theorem vBase_correct : circuit.wires (List.ofFn (fun i : Fin 26 => decide (i = Fin.castAdd 13 (0 : Fin 13)))) = vBase := by rfl

theorem wBase_correct : circuit.wires (List.ofFn (fun i : Fin 26 => decide (i = Fin.natAdd 13 (0 : Fin 13)))) = wBase := by rfl

def share (x : Fin 26 → Bool) (t : Fin 13) : Bool :=
  (x (Fin.castAdd 13 t) || x (Fin.castAdd 13 (t + 1))) ||
  (x (Fin.castAdd 13 (t + 3)) || x (Fin.castAdd 13 (t + 9)))

def star (x : Fin 26 → Bool) (t : Fin 13) : Bool := x (Fin.natAdd 13 t) && share x t

theorem split_gate (a b c : Bool) : ((a || b) && (a || c)) = (a || (c && b)) := by
  cases a <;> cases b <;> cases c <;> rfl

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

-- Verify each gate against the proposed complete wire table using earlier wires.
def valid (table : List Bool) (offset : ℕ) : List Gate → List Bool → Prop
  | [], [] => True
  | g :: gs, b :: bs =>
    g.op.eval (g.inputs.map fun i => if i < offset then table.getD i false else false) = b ∧
    valid table (offset + 1) gs bs
  | _, _ => False

theorem valid_sound (gs : List Gate) (pre post table : List Bool) (join : table = pre ++ post)
    (cert : valid table pre.length gs post) : gs.foldl gateStep pre = table := by
  induction gs generalizing pre post with
  | nil =>
    cases post with
    | nil => simpa using join.symm
    | cons b bs => exact cert.elim
  | cons g gs ih =>
    cases post with
    | nil => exact cert.elim
    | cons b bs =>
      obtain ⟨head, tail⟩ := cert
      have agree : g.inputs.map (fun i => pre.getD i false) = g.inputs.map
          (fun i => if i < pre.length then table.getD i false else false) := by
        apply List.map_congr_left
        intro i _
        by_cases early : i < pre.length
        · simp [early, join, List.getD_eq_getElem?_getD, List.getElem?_append_left early]
        · simp [early, List.getD_eq_getElem?_getD]
      change gs.foldl gateStep (pre ++ [g.op.eval (g.inputs.map fun i => pre.getD i false)]) = table
      rw [agree, head]
      apply ih (pre ++ [b]) bs
      · simpa [List.append_assoc] using join
      · simpa using tail

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
-- The certificate gives one Boolean expression per wire.
theorem output (x : Fin 26 → Bool) : circuit.eval (List.ofFn x) = ((((((((((((star x 0 || star x 1) || star x 2) || star x 3) || star x 4) || star x 5) || star x 6) || star x 7) || star x 8) || star x 9) || star x 10) || star x 11) || star x 12) := by
  let b0 : Bool := x 0 || x 1
  let b1 : Bool := x 3 || x 9
  let b2 : Bool := b0 || b1
  let b3 : Bool := x 1 || x 2
  let b4 : Bool := x 4 || x 10
  let b5 : Bool := b3 || b4
  let b6 : Bool := x 2 || x 3
  let b7 : Bool := x 5 || x 11
  let b8 : Bool := b6 || b7
  let b9 : Bool := x 3 || x 4
  let b10 : Bool := x 6 || x 12
  let b11 : Bool := b9 || b10
  let b12 : Bool := x 4 || x 5
  let b13 : Bool := x 7 || x 0
  let b14 : Bool := b12 || b13
  let b15 : Bool := x 5 || x 6
  let b16 : Bool := x 8 || x 1
  let b17 : Bool := b15 || b16
  let b18 : Bool := x 6 || x 7
  let b19 : Bool := x 9 || x 2
  let b20 : Bool := b18 || b19
  let b21 : Bool := x 7 || x 8
  let b22 : Bool := x 10 || x 3
  let b23 : Bool := b21 || b22
  let b24 : Bool := x 8 || x 9
  let b25 : Bool := x 11 || x 4
  let b26 : Bool := b24 || b25
  let b27 : Bool := x 9 || x 10
  let b28 : Bool := x 12 || x 5
  let b29 : Bool := b27 || b28
  let b30 : Bool := x 10 || x 11
  let b31 : Bool := x 0 || x 6
  let b32 : Bool := b30 || b31
  let b33 : Bool := x 11 || x 12
  let b34 : Bool := x 1 || x 7
  let b35 : Bool := b33 || b34
  let b36 : Bool := x 12 || x 0
  let b37 : Bool := x 2 || x 8
  let b38 : Bool := b36 || b37
  let b39 : Bool := x 13 && b2
  let b40 : Bool := b39 || b5
  let b41 : Bool := b39 || x 14
  let b42 : Bool := b40 && b41
  let b43 : Bool := x 15 && b8
  let b44 : Bool := x 16 && b11
  let b45 : Bool := x 17 && b14
  let b46 : Bool := x 18 && b17
  let b47 : Bool := x 19 && b20
  let b48 : Bool := x 20 && b23
  let b49 : Bool := x 21 && b26
  let b50 : Bool := x 22 && b29
  let b51 : Bool := x 23 && b32
  let b52 : Bool := x 24 && b35
  let b53 : Bool := x 25 && b38
  let b54 : Bool := b42 || b43
  let b55 : Bool := b54 || b44
  let b56 : Bool := b55 || b45
  let b57 : Bool := b56 || b46
  let b58 : Bool := b57 || b47
  let b59 : Bool := b58 || b48
  let b60 : Bool := b59 || b49
  let b61 : Bool := b60 || b50
  let b62 : Bool := b61 || b51
  let b63 : Bool := b62 || b52
  let b64 : Bool := b63 || b53
  let ins : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25]
  let trail : List Bool := [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64]
  let table : List Bool := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64]
  have cert : valid table 26 circuit.gates trail := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
    · change (x 0 || (x 1 || false)) = b0
      simp only [Bool.or_false]
      rfl
    · change (x 3 || (x 9 || false)) = b1
      simp only [Bool.or_false]
      rfl
    · change (b0 || (b1 || false)) = b2
      simp only [Bool.or_false]
      rfl
    · change (x 1 || (x 2 || false)) = b3
      simp only [Bool.or_false]
      rfl
    · change (x 4 || (x 10 || false)) = b4
      simp only [Bool.or_false]
      rfl
    · change (b3 || (b4 || false)) = b5
      simp only [Bool.or_false]
      rfl
    · change (x 2 || (x 3 || false)) = b6
      simp only [Bool.or_false]
      rfl
    · change (x 5 || (x 11 || false)) = b7
      simp only [Bool.or_false]
      rfl
    · change (b6 || (b7 || false)) = b8
      simp only [Bool.or_false]
      rfl
    · change (x 3 || (x 4 || false)) = b9
      simp only [Bool.or_false]
      rfl
    · change (x 6 || (x 12 || false)) = b10
      simp only [Bool.or_false]
      rfl
    · change (b9 || (b10 || false)) = b11
      simp only [Bool.or_false]
      rfl
    · change (x 4 || (x 5 || false)) = b12
      simp only [Bool.or_false]
      rfl
    · change (x 7 || (x 0 || false)) = b13
      simp only [Bool.or_false]
      rfl
    · change (b12 || (b13 || false)) = b14
      simp only [Bool.or_false]
      rfl
    · change (x 5 || (x 6 || false)) = b15
      simp only [Bool.or_false]
      rfl
    · change (x 8 || (x 1 || false)) = b16
      simp only [Bool.or_false]
      rfl
    · change (b15 || (b16 || false)) = b17
      simp only [Bool.or_false]
      rfl
    · change (x 6 || (x 7 || false)) = b18
      simp only [Bool.or_false]
      rfl
    · change (x 9 || (x 2 || false)) = b19
      simp only [Bool.or_false]
      rfl
    · change (b18 || (b19 || false)) = b20
      simp only [Bool.or_false]
      rfl
    · change (x 7 || (x 8 || false)) = b21
      simp only [Bool.or_false]
      rfl
    · change (x 10 || (x 3 || false)) = b22
      simp only [Bool.or_false]
      rfl
    · change (b21 || (b22 || false)) = b23
      simp only [Bool.or_false]
      rfl
    · change (x 8 || (x 9 || false)) = b24
      simp only [Bool.or_false]
      rfl
    · change (x 11 || (x 4 || false)) = b25
      simp only [Bool.or_false]
      rfl
    · change (b24 || (b25 || false)) = b26
      simp only [Bool.or_false]
      rfl
    · change (x 9 || (x 10 || false)) = b27
      simp only [Bool.or_false]
      rfl
    · change (x 12 || (x 5 || false)) = b28
      simp only [Bool.or_false]
      rfl
    · change (b27 || (b28 || false)) = b29
      simp only [Bool.or_false]
      rfl
    · change (x 10 || (x 11 || false)) = b30
      simp only [Bool.or_false]
      rfl
    · change (x 0 || (x 6 || false)) = b31
      simp only [Bool.or_false]
      rfl
    · change (b30 || (b31 || false)) = b32
      simp only [Bool.or_false]
      rfl
    · change (x 11 || (x 12 || false)) = b33
      simp only [Bool.or_false]
      rfl
    · change (x 1 || (x 7 || false)) = b34
      simp only [Bool.or_false]
      rfl
    · change (b33 || (b34 || false)) = b35
      simp only [Bool.or_false]
      rfl
    · change (x 12 || (x 0 || false)) = b36
      simp only [Bool.or_false]
      rfl
    · change (x 2 || (x 8 || false)) = b37
      simp only [Bool.or_false]
      rfl
    · change (b36 || (b37 || false)) = b38
      simp only [Bool.or_false]
      rfl
    · change (x 13 && (b2 && true)) = b39
      simp only [Bool.and_true]
      rfl
    · change (b39 || (b5 || false)) = b40
      simp only [Bool.or_false]
      rfl
    · change (b39 || (x 14 || false)) = b41
      simp only [Bool.or_false]
      rfl
    · change (b40 && (b41 && true)) = b42
      simp only [Bool.and_true]
      rfl
    · change (x 15 && (b8 && true)) = b43
      simp only [Bool.and_true]
      rfl
    · change (x 16 && (b11 && true)) = b44
      simp only [Bool.and_true]
      rfl
    · change (x 17 && (b14 && true)) = b45
      simp only [Bool.and_true]
      rfl
    · change (x 18 && (b17 && true)) = b46
      simp only [Bool.and_true]
      rfl
    · change (x 19 && (b20 && true)) = b47
      simp only [Bool.and_true]
      rfl
    · change (x 20 && (b23 && true)) = b48
      simp only [Bool.and_true]
      rfl
    · change (x 21 && (b26 && true)) = b49
      simp only [Bool.and_true]
      rfl
    · change (x 22 && (b29 && true)) = b50
      simp only [Bool.and_true]
      rfl
    · change (x 23 && (b32 && true)) = b51
      simp only [Bool.and_true]
      rfl
    · change (x 24 && (b35 && true)) = b52
      simp only [Bool.and_true]
      rfl
    · change (x 25 && (b38 && true)) = b53
      simp only [Bool.and_true]
      rfl
    · change (b42 || (b43 || false)) = b54
      simp only [Bool.or_false]
      rfl
    · change (b54 || (b44 || false)) = b55
      simp only [Bool.or_false]
      rfl
    · change (b55 || (b45 || false)) = b56
      simp only [Bool.or_false]
      rfl
    · change (b56 || (b46 || false)) = b57
      simp only [Bool.or_false]
      rfl
    · change (b57 || (b47 || false)) = b58
      simp only [Bool.or_false]
      rfl
    · change (b58 || (b48 || false)) = b59
      simp only [Bool.or_false]
      rfl
    · change (b59 || (b49 || false)) = b60
      simp only [Bool.or_false]
      rfl
    · change (b60 || (b50 || false)) = b61
      simp only [Bool.or_false]
      rfl
    · change (b61 || (b51 || false)) = b62
      simp only [Bool.or_false]
      rfl
    · change (b62 || (b52 || false)) = b63
      simp only [Bool.or_false]
      rfl
    · change (b63 || (b53 || false)) = b64
      simp only [Bool.or_false]
      rfl
  have rows := valid_sound circuit.gates ins trail table (by rfl) cert
  change (circuit.gates.foldl gateStep ins).getD 90 false = _
  rw [rows]
  change ((((((((((((((x 13 && ((x 0 || x 1) || (x 3 || x 9))) || ((x 1 || x 2) || (x 4 || x 10))) && ((x 13 && ((x 0 || x 1) || (x 3 || x 9))) || x 14)) || (x 15 && ((x 2 || x 3) || (x 5 || x 11)))) || (x 16 && ((x 3 || x 4) || (x 6 || x 12)))) || (x 17 && ((x 4 || x 5) || (x 7 || x 0)))) || (x 18 && ((x 5 || x 6) || (x 8 || x 1)))) || (x 19 && ((x 6 || x 7) || (x 9 || x 2)))) || (x 20 && ((x 7 || x 8) || (x 10 || x 3)))) || (x 21 && ((x 8 || x 9) || (x 11 || x 4)))) || (x 22 && ((x 9 || x 10) || (x 12 || x 5)))) || (x 23 && ((x 10 || x 11) || (x 0 || x 6)))) || (x 24 && ((x 11 || x 12) || (x 1 || x 7)))) || (x 25 && ((x 12 || x 0) || (x 2 || x 8)))) = _
  rw [split_gate]
  rfl

theorem incidence (x : Fin 26 → Bool) : circuit.eval (List.ofFn x) = true ↔
  ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧
    x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true := by
  have one (t : Fin 13) : star x t = true ↔ ∃ u : Fin 13,
      (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true := by
    simp only [star, share, Bool.and_eq_true, Bool.or_eq_true]
    constructor
    · rintro ⟨hl, ((hp | hp) | (hp | hp))⟩
      · exact ⟨t, Or.inl rfl, hp, hl⟩
      · exact ⟨t + 1, Or.inr (Or.inl rfl), hp, hl⟩
      · exact ⟨t + 3, Or.inr (Or.inr (Or.inl rfl)), hp, hl⟩
      · exact ⟨t + 9, Or.inr (Or.inr (Or.inr rfl)), hp, hl⟩
    · rintro ⟨u, (rfl | rfl | rfl | rfl), hp, hl⟩
      · exact ⟨hl, Or.inl (Or.inl hp)⟩
      · exact ⟨hl, Or.inl (Or.inr hp)⟩
      · exact ⟨hl, Or.inr (Or.inl hp)⟩
      · exact ⟨hl, Or.inr (Or.inr hp)⟩
  have finite : circuit.eval (List.ofFn x) = true ↔ ∃ t : Fin 13, star x t = true := by
    rw [output]
    simp only [Bool.or_eq_true]
    constructor
    · rintro ((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
      · exact ⟨3, h⟩
      · exact ⟨4, h⟩
      · exact ⟨5, h⟩
      · exact ⟨6, h⟩
      · exact ⟨7, h⟩
      · exact ⟨8, h⟩
      · exact ⟨9, h⟩
      · exact ⟨10, h⟩
      · exact ⟨11, h⟩
      · exact ⟨12, h⟩
    · rintro ⟨t, h⟩
      fin_cases t
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  rw [finite]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨u, hu⟩ := (one t).mp ht
    exact ⟨u, t, hu⟩
  · rintro ⟨u, t, hu⟩
    exact ⟨t, (one t).mpr ⟨u, hu⟩⟩


def law (base : List Bool) (d : ℕ → Bool) (k : ℕ) (g : Gate) (a b : ℕ) : Prop :=
  (g.op = GateOp.and → d (26 + k) = ((base.getD a false && d b) || (d a && base.getD b false))) ∧
  (g.op = GateOp.or → d (26 + k) = (d a || d b))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
theorem gate_checks : ∀ j : Fin circuit.gates.length,
    let g := circuit.gates.get j
    let a := g.inputs.getD 0 0
    let b := g.inputs.getD 1 0
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j.val ∧ b < 26 + j.val ∧
      law vBase v j.val g a b ∧ law wBase w j.val g a b := by
  let _ : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold law
  decide

theorem gates_ok : ∀ (j : ℕ) (g : Gate), circuit.gates[j]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j ∧ b < 26+j := by
  intro j g hg
  obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  obtain ⟨op, ins, ne, la, lb, _, _⟩ := gate_checks ⟨j,h⟩
  exact ⟨op, _, _, ins, ne, la, lb⟩

theorem mark_laws (k : ℕ) (g : Gate) (a b : ℕ) (hg : circuit.gates[k]? = some g) (hi : g.inputs = [a,b]) :
    law vBase v k g a b ∧ law wBase w k g a b := by
  obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  obtain ⟨_, _, _, _, _, v_ok, w_ok⟩ := gate_checks ⟨k,h⟩
  change law vBase v k circuit.gates[k] (circuit.gates[k].inputs.getD 0 0) (circuit.gates[k].inputs.getD 1 0) at v_ok
  change law wBase w k circuit.gates[k] (circuit.gates[k].inputs.getD 0 0) (circuit.gates[k].inputs.getD 1 0) at w_ok
  simpa [hi] using And.intro v_ok w_ok

-- This is the existence statement paired with L-meta-1482, with budget 65.
theorem exists_65 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 65 ∧
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧
      ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        (∃ v : ℕ → Bool, (∀ my : Fin 13, v my.val = false ∧ v (13 + my.val) = decide (my = l)) ∧
          (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (26 + ky) = (((C.wires (List.ofFn (fun iy : Fin 26 => decide (iy = Fin.castAdd 13 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 26 => decide (ey = Fin.castAdd 13 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (26 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧
        (∃ w : ℕ → Bool, (∀ mx : Fin 13, w mx.val = decide (mx = p) ∧ w (13 + mx.val) = false) ∧
          (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (26 + kx) = (((C.wires (List.ofFn (fun ix : Fin 26 => decide (ix = Fin.natAdd 13 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 26 => decide (ex = Fin.natAdd 13 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (26 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  refine ⟨circuit, by decide, gates_ok, incidence, 0, 0, Or.inl rfl, ?_, ?_⟩
  · refine ⟨v, by decide, ?_, by decide⟩
    intro k g a b hg hi
    rw [vBase_correct]
    exact (mark_laws k g a b hg hi).1
  · refine ⟨w, by decide, ?_, by decide⟩
    intro k g a b hg hi
    rw [wBase_correct]
    exact (mark_laws k g a b hg hi).2

end PlaneDoubleRead
