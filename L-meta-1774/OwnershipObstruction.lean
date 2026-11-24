import PEqualNP.Defs

-- The wire evaluation, cone, descent, and owns_dom lemmas below are reused
-- from the project's checked L-meta-1600, revision 056ae7099a75.
namespace OwnerObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

open PEqualNP.EdgeOwnership in
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.EdgeOwnership in
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h


lemma ite_true_iff (c : Prop) [Decidable c] (b : Bool) :
    (if c then b else false) = true ↔ c ∧ b = true := by
  by_cases h : c <;> simp [h]

lemma W_and_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) :
    W n C x (n + k) = true ↔ ∀ w ∈ (gateAt C k).inputs, w < n + k ∧ W n C x w = true := by
  rw [W_gate n C x k hk, hop]
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
  constructor
  · intro h w hw
    exact (ite_true_iff _ _).mp (h _ ⟨w, hw, rfl⟩)
  · rintro h b ⟨w, hw, rfl⟩
    exact (ite_true_iff _ _).mpr (h w hw)

lemma W_or_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) :
    W n C x (n + k) = true ↔ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧ W n C x w = true := by
  rw [W_gate n C x k hk, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
  constructor
  · rintro ⟨b, ⟨w, hw, rfl⟩, h⟩
    exact ⟨w, hw, (ite_true_iff _ _).mp h⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨_, ⟨w, hw, rfl⟩, (ite_true_iff _ _).mpr h⟩

open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) :
    ∀ k, k < C.gates.length → ∀ i, InCone n C i k → i < k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk i hi
    obtain ⟨w, _, hn, hlt, h⟩ := (inCone_iff n C i k hk).mp hi
    rcases h with h | h
    · omega
    · have := ih (w - n) (by omega) (by omega) i h
      omega

lemma gate_mono2 (C : Circuit) (hM : Monotone2 C) (k : ℕ) (hk : k < C.gates.length) :
    ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length ≤ 2 := by
  have hg := hM (C.gates[k]) (List.getElem_mem hk)
  rw [← gateAt_eq C k hk] at hg
  have h1 := hg.1
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact ⟨h1, hg.2⟩

def Dom (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) : Prop :=
  ∀ y : Fin n → Bool, y t = true → W n C y w = true

open PEqualNP.EdgeOwnership in
lemma descent (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x : Fin n → Bool) :
    ∀ k, k < C.gates.length → W n C x (n + k) = true →
      (gateAt C k).op = GateOp.and ∨
      (∃ i, InCone n C i k ∧ (gateAt C i).op = GateOp.and ∧ W n C x (n + i) = true) ∨
      (∃ u : Fin n, x u = true ∧ Dom n C u (n + k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hx
    rcases (gate_mono2 C hM k hk).1 with hop | hop
    · exact Or.inl hop
    · obtain ⟨w, hw, hlt, hwx⟩ := (W_or_iff n C x k hk hop).mp hx
      by_cases hwn : w < n
      · right; right
        refine ⟨⟨w, hwn⟩, ?_, ?_⟩
        · rw [← W_input n C x w hwn]; exact hwx
        · intro y hy
          refine (W_or_iff n C y k hk hop).mpr ⟨w, hw, hlt, ?_⟩
          rw [W_input n C y w hwn]; exact hy
      · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
        have he : n + k' - n = k' := by omega
        rcases ih k' (by omega) (by omega) hwx with h | ⟨i, hi, hia, hix⟩ | ⟨u, hu, hdom⟩
        · right; left
          exact ⟨k', (inCone_iff n C k' k hk).mpr ⟨n + k', hw, by omega, hlt, Or.inl (by omega)⟩,
            h, hwx⟩
        · right; left
          exact ⟨i, (inCone_iff n C i k hk).mpr
            ⟨n + k', hw, by omega, hlt, Or.inr (by rw [he]; exact hi)⟩, hia, hix⟩
        · right; right
          exact ⟨u, hu, fun y hy => (W_or_iff n C y k hk hop).mpr ⟨n + k', hw, hlt, hdom y hy⟩⟩

open PEqualNP.EdgeOwnership in
lemma owns_dom (n : ℕ) (C : Circuit) (hM : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (p q : Fin n) (ho : Owns n C j p q) :
    ∀ w ∈ (gateAt C j).inputs, w < n + j ∧ (Dom n C p w ∨ Dom n C q w) := by
  obtain ⟨_, _, hval, hno⟩ := ho
  intro w hw
  have hval' : W n C (pairInput p q) (n + j) = true := hval
  obtain ⟨hlt, hwx⟩ := (W_and_iff n C _ j hj hop).mp hval' w hw
  refine ⟨hlt, ?_⟩
  by_cases hwn : w < n
  · rw [W_input n C _ w hwn] at hwx
    have h' : (⟨w, hwn⟩ : Fin n) = p ∨ (⟨w, hwn⟩ : Fin n) = q := of_decide_eq_true hwx
    rcases h' with h | h
    · left
      intro y hy
      rw [W_input n C y w hwn, h]; exact hy
    · right
      intro y hy
      rw [W_input n C y w hwn, h]; exact hy
  · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
    have he : n + k' - n = k' := by omega
    have hk'j : k' < j := by omega
    have hc : InCone n C k' j :=
      (inCone_iff n C k' j hj).mpr ⟨n + k', hw, by omega, hlt, Or.inl (by omega)⟩
    rcases descent n C hM (pairInput p q) k' (by omega) hwx with h | ⟨i, hi, hia, hix⟩ | ⟨t, ht, hdom⟩
    · have hf : W n C (pairInput p q) (n + k') = false := hno k' hk'j hc h
      rw [hwx] at hf
      exact absurd hf (by simp)
    · have hc2 : InCone n C i j := (inCone_iff n C i j hj).mpr
        ⟨n + k', hw, by omega, hlt, Or.inr (by rw [he]; exact hi)⟩
      have hij := inCone_lt n C j hj i hc2
      have hf : W n C (pairInput p q) (n + i) = false := hno i hij hc2 hia
      rw [hix] at hf
      exact absurd hf (by simp)
    · have h' : t = p ∨ t = q := of_decide_eq_true ht
      rcases h' with h | h
      · left; rw [← h]; exact hdom
      · right; rw [← h]; exact hdom

open PEqualNP.EdgeOwnership

def Single {n : ℕ} (C : Circuit) (j : ℕ) (u : Fin n) : Prop :=
  ∀ x : Fin n → Bool, x u = true → gateVal n C j x = true

def Rectangle {n : ℕ} (C : Circuit) (j : ℕ) (a b c d : Fin n) : Prop :=
  ∀ x : Fin n → Bool, (x a = true ∨ x b = true) → (x c = true ∨ x d = true) →
    gateVal n C j x = true

theorem obstruction {n : ℕ} {C : Circuit} (mono : Monotone2 C) {j : ℕ}
    {a b c d : Fin n} (ab : Owns n C j a b) (cd : Owns n C j c d) :
    Single C j a ∨ Single C j b ∨ Single C j c ∨ Single C j d ∨
    Rectangle C j a c b d ∨ Rectangle C j a d b c := by
  have first := owns_dom n C mono j ab.1 ab.2.1 a b ab
  have second := owns_dom n C mono j cd.1 cd.2.1 c d cd
  have all_true (x : Fin n → Bool)
      (all : ∀ w ∈ (gateAt C j).inputs, W n C x w = true) : gateVal n C j x = true :=
    (W_and_iff n C x j ab.1 ab.2.1).mpr fun w hw => ⟨(first w hw).1, all w hw⟩
  by_cases empty : (gateAt C j).inputs = []
  · left
    exact fun x _ => all_true x (by simp [empty])
  have two : (gateAt C j).inputs.length ≤ 2 := (gate_mono2 C mono j ab.1).2
  obtain ⟨u,v,hu,hv,read⟩ : ∃ u v, u ∈ (gateAt C j).inputs ∧ v ∈ (gateAt C j).inputs ∧
      ∀ w ∈ (gateAt C j).inputs, w = u ∨ w = v := by
    cases hs : (gateAt C j).inputs with
    | nil => exact (empty hs).elim
    | cons u tail =>
      cases tail with
      | nil => exact ⟨u,u,by simp,by simp,by simp⟩
      | cons v rest =>
        have : rest = [] := by simpa [hs] using two
        subst rest
        exact ⟨u,v,by simp,by simp,by simp⟩
  have one (t : Fin n) {s r : ℕ}
      (all : ∀ w ∈ (gateAt C j).inputs, w = s ∨ w = r)
      (left : Dom n C t s) (right : Dom n C t r) : Single C j t := by
    intro x ht
    apply all_true
    intro w hw
    rcases all w hw with rfl | rfl
    · exact left x ht
    · exact right x ht
  have rect (a' b' c' d' : Fin n) {s r : ℕ}
      (all : ∀ w ∈ (gateAt C j).inputs, w = s ∨ w = r)
      (aDom : Dom n C a' s) (bDom : Dom n C b' s)
      (cDom : Dom n C c' r) (dDom : Dom n C d' r) : Rectangle C j a' b' c' d' := by
    intro x left right
    apply all_true
    intro w hw
    rcases all w hw with rfl | rfl
    · exact left.elim (aDom x) (bDom x)
    · exact right.elim (cDom x) (dDom x)
  have orient (s r : ℕ) (hs : s ∈ (gateAt C j).inputs) (hr : r ∈ (gateAt C j).inputs)
      (all : ∀ w ∈ (gateAt C j).inputs, w = s ∨ w = r)
      (ha : Dom n C a s) (hb : Dom n C b r) :
      Single C j c ∨ Single C j d ∨ Rectangle C j a c b d ∨ Rectangle C j a d b c := by
    rcases (second s hs).2 with hsc | hsd <;> rcases (second r hr).2 with hrc | hrd
    · exact Or.inl (one c all hsc hrc)
    · exact Or.inr (Or.inr (Or.inl (rect a c b d all ha hsc hb hrd)))
    · exact Or.inr (Or.inr (Or.inr (rect a d b c all ha hsd hb hrc)))
    · exact Or.inr (Or.inl (one d all hsd hrd))
  rcases (first u hu).2 with hua | hub <;> rcases (first v hv).2 with hva | hvb
  · exact Or.inl (one a read hua hva)
  · exact Or.inr (Or.inr (orient u v hu hv read hua hvb))
  · exact Or.inr (Or.inr (orient v u hv hu (fun w hw => (read w hw).symm) hva hub))
  · exact Or.inr (Or.inl (one b read hub hvb))

theorem operands_are_earlier_ORs {n : ℕ} {C : Circuit} (mono : Monotone2 C) {j : ℕ}
    {a b c d : Fin n} (ab : Owns n C j a b) (cd : Owns n C j c d)
    (ac : a ≠ c) (ad : a ≠ d) (bc : b ≠ c) (bd : b ≠ d) :
    ∀ w ∈ (gateAt C j).inputs, ∃ i < j, w = n + i ∧ (gateAt C i).op = GateOp.or := by
  intro w hw
  obtain ⟨valid, left⟩ := (W_and_iff n C _ j ab.1 ab.2.1).mp ab.2.2.1 w hw
  have right := ((W_and_iff n C _ j cd.1 cd.2.1).mp cd.2.2.1 w hw).2
  by_cases raw : w < n
  · rw [W_input n C _ w raw] at left right
    have x : (⟨w,raw⟩ : Fin n) = a ∨ (⟨w,raw⟩ : Fin n) = b := of_decide_eq_true left
    have y : (⟨w,raw⟩ : Fin n) = c ∨ (⟨w,raw⟩ : Fin n) = d := of_decide_eq_true right
    rcases x with h | h <;> rcases y with k | k
    · exact (ac (h.symm.trans k)).elim
    · exact (ad (h.symm.trans k)).elim
    · exact (bc (h.symm.trans k)).elim
    · exact (bd (h.symm.trans k)).elim
  · let i := w - n
    have eq : w = n + i := by dsimp [i]; omega
    have lt : i < j := by omega
    have cone : InCone n C i j :=
      (inCone_iff n C i j ab.1).mpr ⟨w,hw,by omega,valid,Or.inl rfl⟩
    refine ⟨i, lt, eq, ?_⟩
    rcases (gate_mono2 C mono i (lt.trans ab.1)).1 with op | op
    · have off := ab.2.2.2 i lt cone op
      rw [eq] at left
      change W n C (pairInput a b) (n+i) = false at off
      exact (Bool.false_ne_true (off.symm.trans left)).elim
    · exact op

end OwnerObstruction
