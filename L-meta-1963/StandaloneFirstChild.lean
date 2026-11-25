import PEqualNP.Defs

namespace PlaneTests1963

open PEqualNP.HeptadCover

-- A bit at index i represents the point or line with Singer index i.
def decode (m : Nat) : Finset (Fin 13) :=
  Finset.univ.filter (fun i => m.testBit i.val)

-- The first mask is a quadrangle. The second is exactly its set of exterior lines.
def rows : List (Nat × Nat) := [
  (39, 392), (71, 896), (135, 776), (2055, 648), (83, 644), (275, 580), (2067, 704),
  (4115, 196), (1059, 328), (2083, 200), (4131, 448), (195, 772), (4163, 388), (387, 524),
  (1155, 268), (1283, 76), (2307, 584), (5123, 324), (29, 2592), (77, 2816), (141, 800),
  (1037, 2336), (85, 2688), (533, 2208), (2069, 672), (101, 2432), (549, 2184), (1061, 2312),
  (1157, 296), (2181, 552), (1541, 2088), (2565, 168), (281, 2624), (1049, 2144), (2073, 608),
  (105, 2306), (297, 2114), (1065, 2368), (4137, 322), (201, 770), (329, 2562), (2185, 546),
  (4233, 290), (2313, 578), (5129, 352), (6153, 98), (337, 2564), (593, 2180), (1297, 2116),
  (1553, 2084), (4625, 164), (5137, 100), (6161, 224), (609, 2178), (4193, 386), (801, 2058),
  (1313, 2120), (2337, 74), (2593, 138), (6177, 194), (449, 518), (4289, 262), (833, 2054),
  (4673, 134), (897, 14), (2433, 522), (1665, 44), (2689, 42), (4737, 38), (5249, 292),
  (1793, 2060), (6657, 162), (78, 784), (142, 1792), (270, 1552), (4110, 1296), (166, 1288),
  (550, 1160), (4134, 1408), (2118, 656), (4166, 400), (390, 1544), (774, 1048), (2310, 536),
  (2566, 152), (4614, 1168), (58, 5184), (154, 5632), (282, 1600), (2074, 4672), (170, 5376),
  (1066, 4416), (4138, 1344), (202, 4864), (1098, 4368), (2122, 4624), (2314, 592), (4362, 1104),
  (3082, 4176), (5130, 336), (562, 5248), (2098, 4288), (4146, 1216), (210, 4612), (594, 4228),
  (2130, 4736), (402, 1540), (658, 5124), (4370, 1092), (4626, 1156), (674, 5128), (1186, 4360),
  (2594, 4232), (3106, 4168), (1218, 4356), (1602, 4116), (2626, 4240), (4674, 148), (5186, 276),
  (898, 1036), (1666, 4108), (1794, 28), (4866, 1044), (3330, 88), (5378, 84), (3586, 4120),
  (156, 1568), (284, 3584), (540, 3104), (332, 2576), (1100, 2320), (4236, 1312), (780, 3088),
  (1548, 2096), (4620, 1072), (5132, 304), (116, 2177), (308, 3073), (564, 3200), (4148, 1153),
  (340, 2561), (2132, 641), (404, 1537), (2196, 545), (4244, 1057), (4628, 1184), (6164, 161),
  (1124, 2305), (4196, 385), (420, 1033), (1188, 265), (4260, 1281), (804, 3080), (1316, 2057),
  (1348, 2065), (2372, 529), (5188, 273), (6212, 145), (2436, 521), (3204, 41), (5252, 289),
  (1796, 2072), (3332, 25), (3588, 56), (6660, 176), (7172, 49), (312, 3136), (568, 7168),
  (1080, 6208), (664, 5152), (2200, 4640), (1560, 6176), (3096, 4192), (232, 4354), (616, 6146),
  (1128, 6400), (680, 5122), (4264, 1282), (808, 3074), (4392, 1090), (2248, 4610), (840, 2066),
  (2376, 530), (1608, 6160), (2632, 4114), (2696, 4130), (4744, 1058), (4872, 1042), (6408, 82),
  (3592, 4144), (6664, 50), (7176, 112), (624, 6272), (1136, 6145), (2160, 4225), (1328, 2113),
  (4400, 1089), (3120, 4161), (6192, 193), (464, 517), (1232, 4101), (2256, 4609), (1360, 2053),
  (1616, 6148), (4496, 1029), (1680, 4132), (4752, 1060), (3216, 4129), (5264, 37), (5392, 69),
  (7184, 97), (1248, 4353), (2272, 4099), (4320, 259), (2656, 4226), (6240, 131), (928, 1034),
  (2464, 11), (4512, 1027), (2720, 4106), (3232, 4105), (3360, 73), (6432, 67), (2496, 515),
  (4544, 7), (5312, 261), (1856, 2068), (4928, 22), (5440, 21), (6464, 19), (6720, 146),
  (4992, 1030), (3712, 4136), (7424, 81)]

def tests (dual : Bool) : List Nat :=
  rows.map (fun r => if dual then r.2 else r.1)

def block (dual : Bool) (i : Fin 13) : Nat :=
  (List.finRange 13).foldl (fun m j =>
    if (if dual then i ∈ singerLines3 j else j ∈ singerLines3 i)
    then m ||| (1 <<< j.val) else m) 0

def subset (a b : Nat) : Bool := (a &&& b) == a

-- Masks of all k-subsets of 0,...,n-1, listed by whether they contain n-1.
def masks : Nat → Nat → List Nat
  | _, 0 => [0]
  | 0, _ + 1 => []
  | n + 1, k + 1 => masks n (k + 1) ++ (masks n k).map (fun m => m ||| (1 <<< n))

def eligible (dual : Bool) : List Nat :=
  masks 13 1 ++ masks 13 2 ++
    (masks 13 3).filter (fun s => ! (List.finRange 13).any (fun i => subset s (block dual i)))

-- The intersection of all test sets containing s. Starting with all 13 bits
-- also makes a missing witness fail the forthcoming test.
def forced (dual : Bool) (s : Nat) : Nat :=
  (tests dual).foldl (fun a q => if subset s q then a &&& q else a) 8191

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_geometry :
    rows.all (fun r => decide (IsQuadrangle singerLines3 (decode r.1) ∧
      missLines singerLines3 (decode r.1) = decode r.2 ∧
      (decode r.2).card = 3 ∧
      ∀ p : Fin 13, p ∉ decode r.1 → ∃ l ∈ decode r.2, p ∈ singerLines3 l)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem shore_counts :
    rows.length = 234 ∧ (tests false).Nodup ∧ (tests true).Nodup ∧
      (∀ v : Fin 13, ((tests false).filter (fun m => m.testBit v.val)).length = 72) ∧
      (∀ v : Fin 13, ((tests true).filter (fun m => m.testBit v.val)).length = 54) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem extension_checks :
    (eligible false).all (fun s => forced false s == s) = true ∧
    (eligible true).all (fun s => forced true s == s) = true := by
  decide +kernel

-- A checked intersection certifies a witness for every vertex outside s.
private theorem bit_stays (xs : List Nat) (s a i : Nat) (ha : a.testBit i = true)
    (hh : ∀ q ∈ xs, subset s q = true → q.testBit i = true) :
    (xs.foldl (fun acc q => if subset s q then acc &&& q else acc) a).testBit i = true := by
  induction xs generalizing a with
  | nil => exact ha
  | cons q qs ih =>
    rw [List.foldl_cons]
    apply ih
    · by_cases h : subset s q = true
      · simp [h, ha, hh q (by simp) h]
      · simp [h, ha]
    · intro z hz
      exact hh z (by simp [hz])

theorem extend_avoiding (dual : Bool) (s : Nat) (hs : s ∈ eligible dual) (v : Fin 13)
    (hv : s.testBit v.val = false) :
    ∃ q ∈ tests dual, subset s q = true ∧ q.testBit v.val = false := by
  have hall : (eligible dual).all (fun z => forced dual z == z) = true := by
    cases dual with
    | false => exact extension_checks.1
    | true => exact extension_checks.2
  have heq : forced dual s = s := beq_iff_eq.mp (List.all_eq_true.mp hall s hs)
  by_contra h
  have all_ones : (8191 : Nat).testBit v.val = true := by
    exact (Nat.testBit_two_pow_sub_one 13 v.val).trans (decide_eq_true v.isLt)
  have keep := bit_stays (tests dual) s 8191 v.val all_ones (by
    intro q hq sub
    cases eqn : q.testBit v.val with
    | false => exact (h ⟨q, hq, sub, eqn⟩).elim
    | true => rfl)
  change (forced dual s).testBit v.val = true at keep
  rw [heq, hv] at keep
  contradiction

def bit (i : Fin 13) : Nat := 1 <<< i.val

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem generator_membership :
    (∀ a : Fin 13, bit a ∈ masks 13 1) ∧
    (∀ a b : Fin 13, a ≠ b → bit a ||| bit b ∈ masks 13 2) ∧
    (∀ a b c : Fin 13, a ≠ b → b ≠ c → a ≠ c →
      bit a ||| bit b ||| bit c ∈ masks 13 3) := by
  have check1 : (List.finRange 13).all
      (fun a => (masks 13 1).contains (bit a)) = true := by decide +kernel
  have check2 : (List.finRange 13).all (fun a => (List.finRange 13).all
      (fun b => a == b || (masks 13 2).contains (bit a ||| bit b))) = true := by decide +kernel
  have check3 : (List.finRange 13).all (fun a => (List.finRange 13).all
      (fun b => (List.finRange 13).all (fun c => a == b || b == c || a == c ||
        (masks 13 3).contains (bit a ||| bit b ||| bit c)))) = true := by decide +kernel
  refine ⟨fun a => List.contains_iff_mem.mp (List.all_eq_true.mp check1 a (List.mem_finRange a)), ?_, ?_⟩
  · intro a b hab
    have h := List.all_eq_true.mp (List.all_eq_true.mp check2 a (List.mem_finRange a)) b (List.mem_finRange b)
    simpa [hab] using h
  · intro a b c hab hbc hac
    have h := List.all_eq_true.mp (List.all_eq_true.mp
      (List.all_eq_true.mp check3 a (List.mem_finRange a)) b (List.mem_finRange b)) c (List.mem_finRange c)
    simpa [hab,hbc,hac] using h

theorem singleton_eligible (dual : Bool) (a : Fin 13) : bit a ∈ eligible dual := by
  simp only [eligible, List.mem_append]
  exact Or.inl (Or.inl (generator_membership.1 a))

theorem pair_eligible (dual : Bool) (a b : Fin 13) (hab : a ≠ b) :
    bit a ||| bit b ∈ eligible dual := by
  simp only [eligible, List.mem_append]
  exact Or.inl (Or.inr (generator_membership.2.1 a b hab))

theorem triple_eligible (dual : Bool) (a b c : Fin 13) (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c)
    (noncollinear : ∀ i : Fin 13, subset (bit a ||| bit b ||| bit c) (block dual i) = false) :
    bit a ||| bit b ||| bit c ∈ eligible dual := by
  simp only [eligible, List.mem_append, List.mem_filter, Bool.not_eq_true']
  refine Or.inr ⟨generator_membership.2.2 a b c hab hbc hac, ?_⟩
  simp [List.any_eq_false, noncollinear]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block_incidence :
    ∀ (dual : Bool) (i j : Fin 13), (block dual i).testBit j.val =
      decide (if dual then i ∈ singerLines3 j else j ∈ singerLines3 i) := by
  decide +kernel

theorem subset_decode {s q : Nat} (h : subset s q = true) : decode s ⊆ decode q := by
  intro i hi
  have hs : s.testBit i.val = true := by simpa [decode] using hi
  have heq : s &&& q = s := beq_iff_eq.mp h
  have hb := congrArg (fun m : Nat => m.testBit i.val) heq
  change (s &&& q).testBit i.val = s.testBit i.val at hb
  rw [Nat.testBit_and, hs, Bool.true_and] at hb
  simpa [decode] using hb

theorem project_extension (dual : Bool) (s : Nat) (hs : s ∈ eligible dual)
    (v : Fin 13) (hv : v ∉ decode s) :
    ∃ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q ∧
      let T := if dual then missLines singerLines3 Q else Q
      decode s ⊆ T ∧ v ∉ T := by
  have hv' : s.testBit v.val = false := by simpa [decode] using hv
  obtain ⟨q, hq, hsub, hnot⟩ := extend_avoiding dual s hs v hv'
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  have hgeo := of_decide_eq_true (List.all_eq_true.mp row_geometry r hr)
  refine ⟨decode r.1, hgeo.1, ?_⟩
  cases dual <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hsub hnot ⊢
  · exact ⟨subset_decode hsub, by simpa [decode] using hnot⟩
  · rw [hgeo.2.1]
    exact ⟨subset_decode hsub, by simpa [decode] using hnot⟩


def sideLine (dual : Bool) (i : Fin 13) : Finset (Fin 13) :=
  if dual then Finset.univ.filter (fun j => i ∈ singerLines3 j) else singerLines3 i

theorem decode_block (dual : Bool) (i : Fin 13) : decode (block dual i) = sideLine dual i := by
  ext j
  cases dual <;> simp [decode, sideLine, block_incidence]

theorem decode_bit : ∀ i : Fin 13, decode (bit i) = {i} := by decide +kernel

theorem decode_or (m n : Nat) : decode (m ||| n) = decode m ∪ decode n := by
  ext i
  simp [decode]

-- An off-vertex extension on either shore for actual Finsets in the project plane.
-- For a point-side test T is Q, and for a line-side test T is the set of lines missing Q.
theorem geometric_extension (dual : Bool) (S : Finset (Fin 13)) (v : Fin 13)
    (hpos : 1 ≤ S.card) (hsize : S.card ≤ 3) (outside : v ∉ S)
    (arc : S.card = 3 → ∀ i, ¬ S ⊆ sideLine dual i) :
    ∃ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q ∧
      let T := if dual then missLines singerLines3 Q else Q
      S ⊆ T ∧ v ∉ T := by
  have repr : ∃ m, m ∈ eligible dual ∧ decode m = S := by
    rcases (show S.card = 1 ∨ S.card = 2 ∨ S.card = 3 by omega) with h | h | h
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
      exact ⟨bit a, singleton_eligible dual a, (decode_bit a).trans ha.symm⟩
    · obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp h
      exact ⟨bit a ||| bit b, pair_eligible dual a b hab, by simp [decode_or, decode_bit, hs]⟩
    · obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := Finset.card_eq_three.mp h
      have eq : decode (bit a ||| bit b ||| bit c) = S := by simp [decode_or, decode_bit, hs]
      refine ⟨bit a ||| bit b ||| bit c, triple_eligible dual a b c hab hbc hac ?_, eq⟩
      intro i
      cases z : subset (bit a ||| bit b ||| bit c) (block dual i) with
      | false => rfl
      | true => exact (arc h i (by simpa [eq, decode_block] using subset_decode z)).elim
  obtain ⟨m, hm, eq⟩ := repr
  simpa [eq] using project_extension dual m hm v (by simpa [eq] using outside)

theorem decode_injective_below {m n : Nat} (hm : m < 8192) (hn : n < 8192)
    (h : decode m = decode n) : m = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 13
  · let v : Fin 13 := ⟨i, hi⟩
    have eq : v ∈ decode m ↔ v ∈ decode n := by rw [h]
    have eq' : m.testBit i = true ↔ n.testBit i = true := by simpa [decode, v] using eq
    cases hm' : m.testBit i <;> cases hn' : n.testBit i <;> simp_all
  · have p : 8192 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hi)
    rw [Nat.testBit_lt_two_pow (hm.trans_le p), Nat.testBit_lt_two_pow (hn.trans_le p)]

def testFinsets (dual : Bool) : List (Finset (Fin 13)) := (tests dual).map decode

set_option maxRecDepth 100000 in
theorem distinct_testFinsets (dual : Bool) : (testFinsets dual).Nodup := by
  have bounds : ((tests dual).all fun m => decide (m < 8192)) = true := by
    cases dual <;> decide +kernel
  apply List.Nodup.map_on
  · intro m hm n hn eq
    exact decode_injective_below (of_decide_eq_true (List.all_eq_true.mp bounds m hm))
      (of_decide_eq_true (List.all_eq_true.mp bounds n hn)) eq
  · cases dual with
    | false => exact shore_counts.2.1
    | true => exact shore_counts.2.2.1

theorem testFinsets_through (dual : Bool) (v : Fin 13) :
    ((testFinsets dual).filter (fun s => decide (v ∈ s))).length = if dual then 54 else 72 := by
  simp only [testFinsets, List.filter_map, List.length_map]
  have h : ((fun s : Finset (Fin 13) => decide (v ∈ s)) ∘ decode) =
      fun m => m.testBit v.val := by funext m; simp [decode]
  rw [h]
  cases dual with
  | false => exact shore_counts.2.2.2.1 v
  | true => exact shore_counts.2.2.2.2 v

end PlaneTests1963

open PEqualNP.HeptadCover

namespace Verified1963
theorem solved_extension : ∀ (b : Bool) (S : Finset (Fin 13)) (v : Fin 13),
    1 ≤ S.card → S.card ≤ 3 → v ∉ S → (S.card = 3 → ∀ l : Fin 13, ¬ S ⊆
        (if b then Finset.univ.filter (fun j => l ∈ singerLines3 j) else singerLines3 l)) →
    ∃ Q ∈ quadrangles singerLines3,
      let T := if b then missLines singerLines3 Q else Q
      S ⊆ T ∧ v ∉ T := by
  intro b S v nonempty small outside arc
  obtain ⟨Q, hQ, hfit⟩ := PlaneTests1963.geometric_extension b S v nonempty small outside arc
  exact ⟨Q, by simpa only [quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
    Finset.subset_univ, true_and, IsQuadrangle] using hQ, hfit⟩
end Verified1963
