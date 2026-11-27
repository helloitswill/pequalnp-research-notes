import Std

/-!
An all-zero rectangle consists of a set of rows and a set of columns whose
Cartesian product contains only zeros. The table below is the project matrix
for L-meta-9361 and L-meta-9348. Indices are zero-based. In every mask pair,
bit i of the first mask selects row i and bit j of the second selects column j.
-/
namespace PuncturedPlaneCover

abbrev Index := Fin 21
abbrev Rectangle := (Index → Bool) × (Index → Bool)

def rows : List Nat :=
  [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360,
   82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405,
   204810, 409620, 819240, 1638480]

def entry (i j : Index) : Bool := (rows.getD i.val 0).testBit j.val

def covers (rs : List Rectangle) (i j : Index) : Bool :=
  rs.any fun r => r.1 i && r.2 j

def decode (ab : Nat × Nat) : Rectangle :=
  (fun i => ab.1.testBit i.val, fun j => ab.2.testBit j.val)

def nearCover : List Rectangle := [
    (1070849, 262158), (581680, 197060), (330896, 1581346), (336641, 527434),
    (673286, 1054736), (1179733, 316672), (145408, 49269), (67938, 1720840),
    (229896, 786640), (561283, 75284), (1458186, 39584), (295172, 70761),
    (1049260, 436225), (537672, 82067)].map decode

theorem nearCover_exact : nearCover.length = 14 ∧ ∀ i j : Index,
    covers nearCover i j = (!entry i j && !((i == 11 && j == 12) || (i == 12 && j == 20))) := by
  decide +kernel

theorem counts :
    ((List.finRange 21).flatMap fun i => (List.finRange 21).map fun j => entry i j).count false = 336 ∧
    ((List.finRange 21).flatMap fun i => (List.finRange 21).map fun j => covers nearCover i j).count true = 334 := by
  decide +kernel

-- This second witness covers every zero outside row 0. The first row is
-- removed from each rectangle before transporting the witness.
def masks : List (Nat × Nat) :=
  [(36355, 536604), (1229129, 266752), (82724, 1443912), (1189132, 18465),
   (8314, 770176), (6152, 57971), (590848, 1075602), (21904, 1376294),
   (1607840, 140037), (149700, 1081616), (819221, 79168), (459138, 1576480),
   (1323584, 33931), (188416, 500)]

def initial : List Rectangle := masks.map fun (a, b) =>
  (fun i => decide (i ≠ 0) && a.testBit i.val, fun j => b.testBit j.val)

theorem initial_exact : ∀ i j : Index,
    covers initial i j = (decide (i ≠ 0) && !entry i j) := by decide +kernel

def pull (f g : Index → Index) (r : Rectangle) : Rectangle :=
  (fun i => r.1 (f i), fun j => r.2 (g j))

theorem covers_pull (rs : List Rectangle) (f g : Index → Index) (i j : Index) :
    covers (rs.map (pull f g)) i j = covers rs (f i) (g j) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      change ((r.1 (f i) && r.2 (g j)) || covers (rs.map (pull f g)) i j) = _
      rw [ih]
      rfl

def swap (r : Rectangle) : Rectangle := (r.2, r.1)

theorem covers_swap (rs : List Rectangle) (i j : Index) :
    covers (rs.map swap) i j = covers rs j i := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      change ((r.2 i && r.1 j) || covers (rs.map swap) i j) =
        ((r.1 j && r.2 i) || covers rs j i)
      rw [ih, Bool.and_comm (r.2 i) (r.1 j)]

theorem translate_entry : ∀ s i j : Index, entry (i - s) (j - s) = entry i j := by
  decide +kernel

theorem reflect_entry : ∀ i j : Index, entry (-j) (-i) = entry i j := by decide +kernel

theorem translated_zero : ∀ s i : Index, decide (i - s ≠ 0) = decide (i ≠ s) := by
  decide +kernel

theorem reversed_distinct : ∀ i j : Index, decide (-i ≠ -j) = decide (i ≠ j) := by
  decide +kernel

theorem delete_any_row (s : Index) :
    ∃ rs : List Rectangle, rs.length = 14 ∧
      ∀ i j, covers rs i j = (decide (i ≠ s) && !entry i j) := by
  let back := fun i : Index => i - s
  refine ⟨initial.map (pull back back), ?_, ?_⟩
  · rw [List.length_map]
    rfl
  · intro i j
    rw [covers_pull, initial_exact]
    change (decide (i - s ≠ 0) && !entry (i - s) (j - s)) = _
    rw [translated_zero, translate_entry]

theorem delete_any_column (s : Index) :
    ∃ rs : List Rectangle, rs.length = 14 ∧
      ∀ i j, covers rs i j = (decide (j ≠ s) && !entry i j) := by
  obtain ⟨rs, hlen, exact_row⟩ := delete_any_row (-s)
  let neg := fun i : Index => -i
  refine ⟨(rs.map swap).map (pull neg neg), ?_, ?_⟩
  · simpa only [List.length_map] using hlen
  · intro i j
    rw [covers_pull, covers_swap, exact_row]
    change (decide (-j ≠ -s) && !entry (-j) (-i)) = _
    rw [reversed_distinct, reflect_entry]

end PuncturedPlaneCover
