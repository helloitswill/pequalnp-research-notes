import PEqualNP.Defs

-- The wire, cone, and OR-reachability lemmas through owns_reach are from the
-- project-checked L_meta_1762 at upstream 056ae7099a75e637daeae581dfdbd0a4c3713d4a.
namespace GateTracing

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

def Reach (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) : Prop :=
  ∀ P : ℕ → Prop, P t.val →
    (∀ k, k < C.gates.length → (gateAt C k).op = GateOp.or →
      ∀ a ∈ (gateAt C k).inputs, a < n + k → P a → P (n + k)) → P w

lemma reach_refl (n : ℕ) (C : Circuit) (t : Fin n) : Reach n C t t.val := fun _ h _ => h

lemma reach_step (n : ℕ) (C : Circuit) (t : Fin n) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a : ℕ) (ha : a ∈ (gateAt C k).inputs)
    (hlt : a < n + k) (h : Reach n C t a) : Reach n C t (n + k) :=
  fun P h0 hs => hs k hk hop a ha hlt (h P h0 hs)

lemma reach_inv (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) (h : Reach n C t w) :
    w = t.val ∨ ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
      ∃ a ∈ (gateAt C k).inputs, a < n + k ∧ Reach n C t a := by
  have h2 := h (fun w => Reach n C t w ∧ (w = t.val ∨ ∃ k, k < C.gates.length ∧ w = n + k ∧
      (gateAt C k).op = GateOp.or ∧ ∃ a ∈ (gateAt C k).inputs, a < n + k ∧ Reach n C t a))
    ⟨reach_refl n C t, Or.inl rfl⟩
    (fun k hk hop a ha hlt ih => ⟨reach_step n C t k hk hop a ha hlt ih.1,
      Or.inr ⟨k, hk, rfl, hop, a, ha, hlt, ih.1⟩⟩)
  exact h2.2

lemma reach_val (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) (y : Fin n → Bool)
    (hy : y t = true) (h : Reach n C t w) : W n C y w = true :=
  h (fun w => W n C y w = true) (by rw [W_input n C y t.val t.isLt]; exact hy)
    (fun k hk hop a ha hlt ih => (W_or_iff n C y k hk hop).mpr ⟨a, ha, hlt, ih⟩)

open PEqualNP.EdgeOwnership in
lemma descent (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x : Fin n → Bool) :
    ∀ k, k < C.gates.length → W n C x (n + k) = true →
      (gateAt C k).op = GateOp.and ∨
      (∃ i, InCone n C i k ∧ (gateAt C i).op = GateOp.and ∧ W n C x (n + i) = true) ∨
      (∃ u : Fin n, x u = true ∧ Reach n C u (n + k)) := by
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
        · exact reach_step n C ⟨w, hwn⟩ k hk hop w hw hlt (reach_refl n C ⟨w, hwn⟩)
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
          exact ⟨u, hu, reach_step n C u k hk hop (n + k') hw hlt hdom⟩

open PEqualNP.EdgeOwnership in
lemma owns_reach (n : ℕ) (C : Circuit) (hM : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (p q : Fin n) (ho : Owns n C j p q) :
    ∀ w ∈ (gateAt C j).inputs, w < n + j ∧ (Reach n C p w ∨ Reach n C q w) := by
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
      rw [← h]; exact reach_refl n C ⟨w, hwn⟩
    · right
      rw [← h]; exact reach_refl n C ⟨w, hwn⟩
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

-- The witness uses only vertices of the two originally owned pairs.
theorem local_false_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (noFour : PEqualNP.TopForm.NoFourCycle G)
    (C : Circuit) (mono : Monotone2 C) (j : ℕ) (p q r s : Fin n)
    (first : Owns n C j p q) (second : Owns n C j r s)
    (pr : p ≠ r) (ps : p ≠ s) (qr : q ≠ r) (qs : q ≠ s) :
    ∃ u ∈ ({p,q,r,s} : Finset (Fin n)), ∃ v ∈ ({p,q,r,s} : Finset (Fin n)),
      gateVal n C j (pairInput u v) = true ∧ ¬ G.Adj u v := by
  classical
  let U : Finset (Fin n) := {p,q,r,s}
  change ∃ u ∈ U, ∃ v ∈ U, _
  by_contra noWitness
  have clean (x y : Fin n) (hx : x ∈ U) (hy : y ∈ U)
      (active : W n C (pairInput x y) (n+j) = true) : G.Adj x y := by
    by_contra notEdge
    exact noWitness ⟨x,hx,y,hy,active,notEdge⟩
  have pick {x y : Fin n} (owned : Owns n C j x y) (w : ℕ)
      (hw : w ∈ (gateAt C j).inputs) : ∃ z : Fin n, (z = x ∨ z = y) ∧ Reach n C z w := by
    rcases (owns_reach n C mono j first.1 first.2.1 x y owned w hw).2 with h | h
    · exact ⟨x,Or.inl rfl,h⟩
    · exact ⟨y,Or.inr rfl,h⟩
  have inFirst {x : Fin n} (h : x = p ∨ x = q) : x ∈ U := by rcases h with rfl | rfl <;> simp [U]
  have inSecond {x : Fin n} (h : x = r ∨ x = s) : x ∈ U := by rcases h with rfl | rfl <;> simp [U]
  have apart {x y : Fin n} (h : x = p ∨ x = q) (k : y = r ∨ y = s) : x ≠ y := by
    rcases h with rfl | rfl <;> rcases k with rfl | rfl <;> assumption
  have back (w : ℕ) (hw : w ∈ (gateAt C j).inputs) : w < n+j :=
    (owns_reach n C mono j first.1 first.2.1 p q first w hw).1
  have arity := (gate_mono2 C mono j first.1).2
  rcases gates : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c,rest⟩⟩⟩
  · apply (G.loopless.irrefl p)
    apply clean p p (by simp [U]) (by simp [U])
    apply (W_and_iff n C _ j first.1 first.2.1).mpr
    simp [gates]
  · have ha : a ∈ (gateAt C j).inputs := by simp [gates]
    obtain ⟨x,hx,rx⟩ := pick first a ha
    apply (G.loopless.irrefl x)
    apply clean x x (inFirst hx) (inFirst hx)
    apply (W_and_iff n C _ j first.1 first.2.1).mpr
    intro w hw
    have eq : w = a := by simpa [gates] using hw
    subst w
    exact ⟨back a ha, reach_val n C x a _ (by simp [pairInput]) rx⟩
  · have ha : a ∈ (gateAt C j).inputs := by simp [gates]
    have hb : b ∈ (gateAt C j).inputs := by simp [gates]
    obtain ⟨x,hx,rx⟩ := pick first a ha
    obtain ⟨y,hy,ry⟩ := pick first b hb
    obtain ⟨z,hz,rz⟩ := pick second a ha
    obtain ⟨t,ht,rt⟩ := pick second b hb
    have cross (i k : Fin n) (hi : i ∈ U) (hk : k ∈ U) (ri : Reach n C i a) (rk : Reach n C k b) :
        G.Adj i k := by
      apply clean i k hi hk
      apply (W_and_iff n C _ j first.1 first.2.1).mpr
      intro w hw
      have hw' : w = a ∨ w = b := by simpa [gates] using hw
      rcases hw' with rfl | rfl
      · exact ⟨back _ ha, reach_val n C i _ _ (by simp [pairInput]) ri⟩
      · exact ⟨back _ hb, reach_val n C k _ _ (by simp [pairInput]) rk⟩
    have small := noFour x z (apart hx hz)
    have subset : ({y,t} : Finset (Fin n)) ⊆ Finset.univ.filter (fun v => G.Adj x v ∧ G.Adj z v) := by
      intro v hv
      rcases (by simpa using hv : v = y ∨ v = t) with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,cross _ _ (inFirst hx) (inFirst hy) rx ry,
          cross _ _ (inSecond hz) (inFirst hy) rz ry⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,cross _ _ (inFirst hx) (inSecond ht) rx rt,
          cross _ _ (inSecond hz) (inSecond ht) rz rt⟩
    have bad := (Finset.card_le_card subset).trans small
    simp [apart hy ht] at bad
  · simp [gates] at arity

lemma wire_monotone {n : ℕ} (C : Circuit) (mono : Monotone2 C) (x y : Fin n → Bool)
    (inc : ∀ t, x t = true → y t = true) (w : ℕ) :
    W n C x w = true → W n C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro active
    by_cases raw : w < n
    · rw [W_input n C x w raw] at active
      rw [W_input n C y w raw]
      exact inc _ active
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    by_cases valid : k < C.gates.length
    · rcases (gate_mono2 C mono k valid).1 with meet | join
      · apply (W_and_iff n C y k valid meet).mpr
        intro t ht
        obtain ⟨lt, on⟩ := (W_and_iff n C x k valid meet).mp active t ht
        exact ⟨lt, ih t lt on⟩
      · obtain ⟨t, ht, lt, on⟩ := (W_or_iff n C x k valid join).mp active
        exact (W_or_iff n C y k valid join).mpr ⟨t, ht, lt, ih t lt on⟩
    · unfold W at active
      rw [getD_ge_length _ _ (by rw [wires_length]; omega)] at active
      contradiction

-- Each retained vertex belongs to a different owned edge. There are four such pairs.
theorem accepted_cross_nonedge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (triangleFree : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (noFour : PEqualNP.TopForm.NoFourCycle G) (C : Circuit) (mono : Monotone2 C)
    (j : ℕ) (p q r s : Fin n) (pq : G.Adj p q) (rs : G.Adj r s)
    (first : Owns n C j p q) (second : Owns n C j r s)
    (pr : p ≠ r) (ps : p ≠ s) (qr : q ≠ r) (qs : q ≠ s) :
    ∃ x y, (x = p ∨ x = q) ∧ (y = r ∨ y = s) ∧ ¬ G.Adj x y ∧
      gateVal n C j (pairInput x y) = true := by
  have swap (a b : Fin n) : pairInput a b = pairInput b a := by
    funext t; simp [pairInput, or_comm]
  have grow (a b : Fin n) (on : gateVal n C j (pairInput a a) = true) :
      gateVal n C j (pairInput a b) = true := by
    apply wire_monotone C mono _ _ _ _ on
    intro t ht
    have eq : t = a := by simpa [pairInput] using ht
    simp [pairInput,eq]
  have pickOther (a b z : Fin n) (edge : G.Adj a b) :
      ∃ y, (y = a ∨ y = b) ∧ ¬ G.Adj z y := by
    by_cases ha : G.Adj z a
    · exact ⟨b, Or.inr rfl, fun hb => triangleFree z a b ha edge hb.symm⟩
    · exact ⟨a, Or.inl rfl, ha⟩
  have same (u v a b : Fin n) (edge : G.Adj a b) (iu : u = a ∨ u = b) (iv : v = a ∨ v = b)
      (miss : ¬ G.Adj u v) : u = v := by
    rcases iu with rfl | rfl <;> rcases iv with rfl | rfl <;> first | rfl | exact (miss edge).elim | exact (miss edge.symm).elim
  obtain ⟨u,hu,v,hv,on,miss⟩ := local_false_pair G noFour C mono j p q r s first second pr ps qr qs
  have classify (t : Fin n) (ht : t ∈ ({p,q,r,s} : Finset (Fin n))) :
      (t = p ∨ t = q) ∨ t = r ∨ t = s := by simpa [or_assoc] using ht
  rcases classify u hu with iu | iu <;> rcases classify v hv with iv | iv
  · obtain rfl := same u v p q pq iu iv miss
    obtain ⟨y,hy,ny⟩ := pickOther r s _ rs
    exact ⟨_,y,iu,hy,ny,grow _ y on⟩
  · exact ⟨u,v,iu,iv,miss,on⟩
  · exact ⟨v,u,iv,iu,fun e => miss e.symm,by rwa [swap]⟩
  · obtain rfl := same u v r s rs iu iv miss
    obtain ⟨x,hx,nx⟩ := pickOther p q _ pq
    exact ⟨x,_,hx,iu,fun e => nx e.symm,by rw [swap]; exact grow _ x on⟩

end GateTracing


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem location_premise : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
    NoFourCycle G → ∀ (C : Circuit), Monotone2 C → ∀ j a b c d,
    G.Adj a b → G.Adj c d → Owns n C j a b → Owns n C j c d →
    a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    ∃ u v, (u = a ∨ u = b) ∧ (v = c ∨ v = d) ∧ ¬ G.Adj u v ∧
      gateVal n C j (pairInput u v) = true := by
  intro n G dec tri sq C mon j a b c d ab cd own1 own2 ac ad bc bd
  exact GateTracing.accepted_cross_nonedge G tri sq C mon j a b c d ab cd own1 own2 ac ad bc bd
