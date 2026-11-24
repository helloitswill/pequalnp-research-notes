import PEqualNP.Defs

namespace OrderFourStar

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A polynomial is a disjunction of positive monomials, including [] for false and [[]] for true.
abbrev Poly := List (List ℕ)

def value (read : ℕ → Bool) (p : Poly) : Bool := p.any (fun m => m.all read)

def product (p q : Poly) : Poly :=
  p.flatMap (fun m => q.map (fun u => m ++ u))

private theorem value_product (read : ℕ → Bool) (p q : Poly) :
    value read (product p q) = (value read p && value read q) := by
  apply Bool.eq_iff_iff.mpr
  simp only [value, product, List.any_eq_true, List.mem_flatMap, List.mem_map, Bool.and_eq_true]
  constructor
  · rintro ⟨m, ⟨u, hu, v, hv, rfl⟩, hm⟩
    rw [List.all_append, Bool.and_eq_true] at hm
    exact ⟨⟨u, hu, hm.1⟩, v, hv, hm.2⟩
  · rintro ⟨⟨u, hu, eu⟩, v, hv, ev⟩
    exact ⟨u ++ v, ⟨u, hu, v, hv, rfl⟩, by simp [eu, ev]⟩

def interp : GateOp → List Poly → Poly
  | .and, ps => ps.foldr product [[]]
  | .or, ps => ps.flatten
  | _, _ => []

private theorem interp_eval (read : ℕ → Bool) (op : GateOp) (ps : List Poly)
    (valid : op = .and ∨ op = .or) :
    value read (interp op ps) = op.eval (ps.map (value read)) := by
  rcases valid with rfl | rfl
  · induction ps with
    | nil => rfl
    | cons p ps ih =>
      change value read (product p (interp .and ps)) = (value read p && GateOp.and.eval (ps.map (value read)))
      rw [value_product, ih]
  · induction ps with
    | nil => rfl
    | cons p ps ih =>
      change value read (p ++ interp .or ps) = (value read p || GateOp.or.eval (ps.map (value read)))
      simpa only [value, List.any_append] using congrArg (fun b => value read p || b) ih

private theorem get_mapped (read : ℕ → Bool) (w : List Poly) (i : ℕ) :
    (w.map (value read)).getD i false = value read (w.getD i []) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> rfl

def step (w : List Poly) (g : Gate) : List Poly :=
  w ++ [interp g.op (g.inputs.map fun i => w.getD i [])]

private def bitStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem fold_interp (read : ℕ → Bool) (gs : List Gate) (w : List Poly)
    (valid : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    (gs.foldl step w).map (value read) = gs.foldl bitStep (w.map (value read)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun u hu => valid u (by simp [hu]))]
    congr 1
    simp only [step, bitStep, List.map_append, List.map_cons, List.map_nil, List.map_map,
      Function.comp_def, interp_eval read g.op _ (valid g (by simp)), get_mapped]

def symbolicOutput (n : ℕ) (C : Circuit) : Poly :=
  (C.gates.foldl step (List.ofFn fun i : Fin n => [[i.val]])).getD C.output []

/-- The symbolic calculation covers every Boolean input simultaneously. -/
theorem symbolic_correct (n : ℕ) (C : Circuit) (mono : Monotone2 C)
    (x : Fin n → Bool) :
    C.eval (List.ofFn x) = value (fun i => (List.ofFn x).getD i false) (symbolicOutput n C) := by
  let read := fun i => (List.ofFn x).getD i false
  let w := List.ofFn (fun i : Fin n => [[i.val]])
  have start : w.map (value read) = List.ofFn x := by
    simp [w, value, read, List.map_ofFn, Function.comp_def, List.getD_eq_getElem?_getD]
  have good (g : Gate) (hg : g ∈ C.gates) : g.op = .and ∨ g.op = .or := by
    simpa using (mono g hg).1
  have cast := fold_interp read C.gates w good
  rw [start] at cast
  change (C.gates.foldl bitStep (List.ofFn x)).getD C.output false = _
  rw [← cast, get_mapped]
  rfl

def row (u : ℕ) : List (ℕ × ℕ) :=
  [(u, 21 + (u + 20) % 21), (u, 21 + u), (u, 21 + (u + 5) % 21),
   (u, 21 + (u + 7) % 21), (u, 21 + (u + 17) % 21)]

def edges := (List.range 21).flatMap row

def starGates (u : ℕ) : List Gate :=
  let first := 42 + 5*u
  [⟨.or, [21 + (u + 20) % 21, 21 + u]⟩,
   ⟨.or, [first, 21 + (u + 5) % 21]⟩,
   ⟨.or, [first+1, 21 + (u + 7) % 21]⟩,
   ⟨.or, [first+2, 21 + (u + 17) % 21]⟩,
   ⟨.and, [u, first+3]⟩]

def mergeGates (j : ℕ) : Gate :=
  ⟨.or, [if j = 0 then 46 else 146+j, 46+5*(j+1)]⟩

def circuit : Circuit :=
  ⟨(List.range 21).flatMap starGates ++ (List.range 20).map mergeGates, 166⟩

private def opNumber : GateOp → ℕ
  | .and => 0
  | .or => 1
  | .not => 2
  | .maj => 3
  | .mod m => m+4

private theorem opNumber_injective : Function.Injective opNumber := by
  intro a b eq
  cases a <;> cases b <;> simp_all [opNumber]

local instance : DecidableEq GateOp := fun a b =>
  if h : opNumber a = opNumber b then isTrue (opNumber_injective h)
    else isFalse (fun eq => h (congrArg opNumber eq))

theorem gate_counts : circuit.size = 125 ∧
    (circuit.gates.filter (fun g => decide (g.op = .or))).length = 104 ∧
    (circuit.gates.filter (fun g => decide (g.op = .and))).length = 21 := by decide +kernel

theorem monotone : Monotone2 circuit := by
  unfold Monotone2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
theorem all_monomials : symbolicOutput 42 circuit = edges.map (fun e => [e.1,e.2]) := by
  decide +kernel

theorem edge_bounds : ∀ e ∈ edges, e.1 < 42 ∧ e.2 < 42 := by decide +kernel

private theorem read_at {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i,hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem realizes_of_symbolic (C : Circuit) (mono : Monotone2 C)
    (symbolic : symbolicOutput 42 C = edges.map (fun e => [e.1,e.2]))
    (x : Fin 42 → Bool) :
    C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val, v.val) ∈ edges ∧
    x u = true ∧ x v = true := by
  rw [symbolic_correct _ _ mono, symbolic]
  simp only [value, List.any_eq_true, List.mem_map]
  constructor
  · rintro ⟨m, ⟨⟨i,j⟩, ij, rfl⟩, ok⟩
    obtain ⟨hi,hj⟩ := edge_bounds _ ij
    change ([i,j].all fun a => (List.ofFn x).getD a false) = true at ok
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      read_at x i hi, read_at x j hj] at ok
    exact ⟨⟨i,hi⟩, ⟨j,hj⟩, ij, ok⟩
  · rintro ⟨u,v,uv,hu,hv⟩
    refine ⟨[u.val,v.val], ⟨(u.val,v.val), uv, rfl⟩, ?_⟩
    simp only [List.all_cons, List.all_nil, Bool.and_true, read_at x u.val u.isLt,
      read_at x v.val v.isLt, hu, hv]


/-- Duplicated variables, differently ordered monomials, and absorbed higher-degree
terms are all allowed by this sufficient certificate for a candidate circuit. -/
theorem realizes_of_cover (C : Circuit) (mono : Monotone2 C)
    (safe : ∀ m ∈ symbolicOutput 42 C, ∃ e ∈ edges, e.1 ∈ m ∧ e.2 ∈ m)
    (complete : ∀ e ∈ edges, ∃ m ∈ symbolicOutput 42 C, ∀ j ∈ m, j = e.1 ∨ j = e.2)
    (x : Fin 42 → Bool) :
    C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val, v.val) ∈ edges ∧
    x u = true ∧ x v = true := by
  rw [symbolic_correct _ _ mono]
  simp only [value, List.any_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨m, hm, yes⟩
    obtain ⟨⟨i,j⟩, edge, left, right⟩ := safe m hm
    obtain ⟨hi, hj⟩ := edge_bounds _ edge
    refine ⟨⟨i,hi⟩, ⟨j,hj⟩, edge, ?_, ?_⟩
    · exact (read_at x i hi).symm.trans (yes i left)
    · exact (read_at x j hj).symm.trans (yes j right)
  · rintro ⟨u,v,edge,onU,onV⟩
    obtain ⟨m,hm,only⟩ := complete (u.val,v.val) edge
    refine ⟨m,hm,fun j hj => ?_⟩
    rcases only j hj with h | h
    · exact (congrArg (fun k => (List.ofFn x).getD k false) h).trans ((read_at x u.val u.isLt).trans onU)
    · exact (congrArg (fun k => (List.ofFn x).getD k false) h).trans ((read_at x v.val v.isLt).trans onV)

theorem realizes (x : Fin 42 → Bool) :
    circuit.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val, v.val) ∈ edges ∧
    x u = true ∧ x v = true := realizes_of_symbolic circuit monotone all_monomials x

theorem or_count :
    {j : Fin circuit.gates.length | (circuit.gates.get j).op = GateOp.or}.ncard = 104 := by
  let ids := Finset.univ.filter (fun j : Fin circuit.gates.length => (circuit.gates.get j).op = GateOp.or)
  have eq : {j : Fin circuit.gates.length | (circuit.gates.get j).op = GateOp.or} =
      (ids : Set (Fin circuit.gates.length)) := by ext j; simp [ids]
  rw [eq, Set.ncard_coe_finset]
  decide +kernel

/-- The exact incidence predicate displayed at L-meta-2378, with the baseline budget. -/
theorem baseline :
    ∃ C : Circuit, Monotone2 C ∧
      (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 42, (u.val, v.val) ∈ List.flatMap
          (fun p : ℕ => [(p, 21+(p+20)%21), (p, 21+p), (p, 21+(p+5)%21),
              (p, 21+(p+7)%21), (p, 21+(p+17)%21)]) (List.range 21) ∧
          x u = true ∧ x v = true) ∧
      {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard = 104 :=
  ⟨circuit, monotone, realizes, or_count⟩

end OrderFourStar
