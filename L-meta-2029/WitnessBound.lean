import PEqualNP.Defs
import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Acyclic


namespace NeighborhoodGirth

variable {n : ℕ} {G : SimpleGraph (Fin n)}

theorem two_step_nonadj
    (girth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    {x u z : Fin n} (xu : G.Adj x u) (uz : G.Adj u z) : ¬ G.Adj x z := by
  intro xz
  let p : G.Walk x x := .cons xu (.cons uz (.cons xz.symm .nil))
  have cycle : p.IsCycle := by
    refine SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, by simp [p]⟩
    simp only [p, SimpleGraph.Walk.tail_cons]
    simp [xu.ne.symm, uz.ne, xz.ne.symm]
  have bound := girth x p cycle
  have length : p.length = 3 := rfl
  omega

-- The square walk and its path check follow the checked proof of L-meta-1601.
theorem common_neighbor_eq
    (girth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    {x u w z : Fin n} (xu : G.Adj x u) (xw : G.Adj x w) (uw : u ≠ w)
    (uz : G.Adj u z) (wz : G.Adj w z) : z = x := by
  by_contra zx
  let p : G.Walk x x := .cons xu (.cons uz (.cons wz.symm (.cons xw.symm .nil)))
  have cycle : p.IsCycle := by
    refine SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, by simp [p]⟩
    simp only [p, SimpleGraph.Walk.tail_cons]
    simp [xu.ne.symm, uz.ne, wz.ne.symm, xw.ne.symm, zx, uw]
  have bound := girth x p cycle
  have length : p.length = 4 := rfl
  omega

end NeighborhoodGirth

/-!
The edge-existence function depends on every nonisolated vertex. Trace the circuit output
backwards: replacing a demanded gate output by at most two input wires increases the
number of demanded wires by at most one. The degree-sum formula then bounds the number
of edges per circuit gate in every family of bounded maximum degree, regardless of girth.
-/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace GraphCircuitSupport

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

/-- Input-wire indices sufficient to determine a set of outputs after evaluating the gate list. -/
def needed : List Gate → ℕ → Finset ℕ → Finset ℕ
  | [], _, out => out
  | g :: gs, m, out =>
    let next := needed gs (m+1) out
    if m ∈ next then next.erase m ∪ g.inputs.toFinset else next

theorem needed_card (gs : List Gate) (m : ℕ) (out : Finset ℕ)
    (fan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (needed gs m out).card ≤ out.card + gs.length := by
  induction gs generalizing m with
  | nil => simp [needed]
  | cons g gs ih =>
    let next := needed gs (m+1) out
    have hnext : next.card ≤ out.card + gs.length :=
      ih (m+1) (fun g hg => fan g (by simp [hg]))
    have small := (List.toFinset_card_le g.inputs).trans (fan g (by simp))
    change (if m ∈ next then next.erase m ∪ g.inputs.toFinset else next).card ≤ _
    by_cases h : m ∈ next
    · rw [ite_eq_left h]
      have hcard := Finset.card_union_le (next.erase m) g.inputs.toFinset
      have rm := Finset.card_erase_add_one h
      simp only [List.length_cons]
      omega
    · rw [ite_eq_right h]
      simp only [List.length_cons]
      omega

/-- Agreement on the backwards trace suffices, including reads beyond the available wires. -/
theorem agrees (gs : List Gate) (m : ℕ) (out : Finset ℕ) (x y : List Bool)
    (lx : x.length = m) (ly : y.length = m)
    (same : ∀ i ∈ needed gs m out, x.getD i false = y.getD i false) :
    ∀ i ∈ out, (gs.foldl gateStep x).getD i false = (gs.foldl gateStep y).getD i false := by
  induction gs generalizing m x y with
  | nil => exact same
  | cons g gs ih =>
    apply ih (m+1) (gateStep x g) (gateStep y g)
      (by simp [gateStep, lx]) (by simp [gateStep, ly])
    let next := needed gs (m+1) out
    change ∀ i ∈ next, _ = _
    change ∀ i ∈ (if m ∈ next then next.erase m ∪ g.inputs.toFinset else next),
      x.getD i false = y.getD i false at same
    intro i hi
    by_cases old : i < m
    · have hx : i < x.length := by omega
      have hy : i < y.length := by omega
      simp only [gateStep,List.getD_eq_getElem?_getD,List.getElem?_append_left hx,
        List.getElem?_append_left hy]
      apply same
      split_ifs
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by omega,hi⟩)
      · exact hi
    · by_cases last : i = m
      · subst i
        rw [ite_eq_left hi] at same
        have hm : g.inputs.map (fun j => x.getD j false) = g.inputs.map (fun j => y.getD j false) :=
          List.map_congr_left (fun j hj => same j (Finset.mem_union_right _ (List.mem_toFinset.mpr hj)))
        simp only [List.getD_eq_getElem?_getD] at hm
        simp only [gateStep, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by omega : x.length ≤ m),
          List.getElem?_append_right (by omega : y.length ≤ m), lx, ly]
        rw [hm]
      · have hx : (gateStep x g).length ≤ i := by simp [gateStep,lx]; omega
        have hy : (gateStep y g).length ≤ i := by simp [gateStep,ly]; omega
        simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none hx,List.getElem?_eq_none hy]

def active {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset (Fin n) :=
  Finset.univ.filter (fun v => ∃ w, G.Adj v w)

def edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) : Bool :=
  decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)

/-- Each nonisolated vertex occurs in the backwards trace of the output. -/
theorem active_subset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit)
    (computes : circuitFun n D = edge G) :
    (active G).image Fin.val ⊆ needed D.gates n {D.output} := by
  classical
  intro k hk
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨w,adj⟩ := (Finset.mem_filter.mp hv).2
  by_contra outside
  let low (i : Fin n) : Bool := decide (i = w)
  let high (i : Fin n) : Bool := decide (i = w ∨ i = v)
  have lowOff : edge G low = false := by
    simp only [edge,decide_eq_false_iff_not,low,decide_eq_true_eq]
    rintro ⟨a,b,h,rfl,rfl⟩
    exact G.loopless.irrefl _ h
  have highOn : edge G high = true := by
    apply decide_eq_true
    exact ⟨v,w,adj,by simp [high],by simp [high]⟩
  have pair : circuitFun n D low = circuitFun n D high := by
    apply agrees D.gates n {D.output} (List.ofFn low) (List.ofFn high) (by simp) (by simp) _ D.output (by simp)
    intro i hi
    by_cases valid : i < n
    · have ne : (⟨i,valid⟩ : Fin n) ≠ v := by
        intro eq
        apply outside
        simpa [← eq] using hi
      simp [List.getD_eq_getElem?_getD, valid, low, high, ne]
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt valid : (List.ofFn low).length ≤ i),
        List.getElem?_eq_none (by simpa using Nat.le_of_not_gt valid : (List.ofFn high).length ≤ i)]
  rw [computes, lowOff, highOn] at pair
  contradiction

/-- A one-hot input at a neighbor witnesses dependence on each nonisolated vertex. -/
theorem active_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit)
    (fan : ∀ g ∈ D.gates, g.inputs.length ≤ 2) (computes : circuitFun n D = edge G) :
    (active G).card ≤ D.size + 1 := by
  have bound := (Finset.card_le_card (active_subset G D computes)).trans (needed_card D.gates n {D.output} fan)
  simpa [Finset.card_image_of_injective _ Fin.val_injective, Circuit.size, Nat.add_comm] using bound

/-- This applies to any number of disjoint copies of a fixed graph with maximum degree `d`. -/
theorem bounded_degree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit)
    (fan : ∀ g ∈ D.gates, g.inputs.length ≤ 2) (computes : circuitFun n D = edge G)
    (d : ℕ) (maxdeg : ∀ v, G.degree v ≤ d) :
    2 * G.edgeFinset.card ≤ d * (D.size + 1) := by
  classical
  have ignore : ∑ v ∈ active G, G.degree v = ∑ v, G.degree v := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ missing
    have no : ¬ ∃ w, G.Adj v w := by simpa [active] using missing
    exact Nat.eq_zero_of_not_pos (fun pos => no ((G.degree_pos_iff_exists_adj v).mp pos))
  calc
    2 * G.edgeFinset.card = ∑ v, G.degree v := G.sum_degrees_eq_twice_card_edges.symm
    _ = ∑ v ∈ active G, G.degree v := ignore.symm
    _ ≤ ∑ _v ∈ active G, d := Finset.sum_le_sum (fun v _ => maxdeg v)
    _ = (active G).card * d := by simp
    _ ≤ d * (D.size + 1) := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left d (active_bound G D fan computes)

/-- A violation at factor `c` requires a vertex of degree greater than `2*c`. -/
theorem high_degree_required {n c : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (mono : Monotone2 D) (computes : circuitFun n D = edge G)
    (violation : c * (D.size + 1) < G.edgeFinset.card) : ∃ v, 2*c < G.degree v := by
  by_contra! bounded
  have h := bounded_degree G D (fun g hg => (mono g hg).2) computes (2*c) bounded
  rw [Nat.mul_assoc] at h
  omega

end GraphCircuitSupport

namespace GirthFiveCounting

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

def live : Finset (Fin n) := Finset.univ.filter (fun v => ∃ w, G.Adj v w)

private theorem filtered_neighbors (x : Fin n) :
    (live G).filter (G.Adj x) = G.neighborFinset x := by
  ext y
  simp only [live, Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.mem_neighborFinset]
  exact ⟨And.right, fun h => ⟨⟨x, h.symm⟩, h⟩⟩

/-- The branch through u consists of u and the vertices reached in two steps through u. -/
private def branch (x u : Fin n) :=
  insert u ((G.neighborFinset u).erase x)

theorem row_bound
    (tri : ∀ {x u z}, G.Adj x u → G.Adj u z → ¬ G.Adj x z)
    (square : ∀ {x u w z}, G.Adj x u → G.Adj x w → u ≠ w →
       G.Adj u z → G.Adj w z → z = x) (x : Fin n) :
    ∑ u ∈ G.neighborFinset x, G.degree u ≤ (live G).card - 1 := by
  classical
  have sizes (u : Fin n) (hu : u ∈ G.neighborFinset x) : (branch G x u).card = G.degree u := by
    have hx : x ∈ G.neighborFinset u := (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hu).symm
    have hself : u ∉ (G.neighborFinset u).erase x := by simp
    rw [branch, Finset.card_insert_of_notMem hself, Finset.card_erase_add_one hx,
      G.card_neighborFinset_eq_degree]
  have disj : (G.neighborFinset x : Set (Fin n)).PairwiseDisjoint (branch G x) := by
    intro u hu w hw huw
    rw [Function.onFun, Finset.disjoint_left]
    have xu := (G.mem_neighborFinset _ _).mp hu
    have xw := (G.mem_neighborFinset _ _).mp hw
    intro z hz hzz
    simp only [branch, Finset.mem_insert, Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hz hzz
    rcases hz with rfl | ⟨hz, uz⟩
    · rcases hzz with eq | ⟨_, wu⟩
      · exact huw eq
      · exact tri xw wu xu
    · rcases hzz with rfl | ⟨_, wz⟩
      · exact tri xu uz xw
      · exact hz (square xu xw huw uz wz)
  have contained : (G.neighborFinset x).biUnion (branch G x) ⊆ (live G).erase x := by
    intro z hz
    obtain ⟨u,hu,hz⟩ := Finset.mem_biUnion.mp hz
    have xu := (G.mem_neighborFinset _ _).mp hu
    simp only [branch, Finset.mem_insert, Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hz
    simp only [Finset.mem_erase, live, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hz with rfl | ⟨hz,uz⟩
    · exact ⟨xu.ne.symm, x, xu.symm⟩
    · exact ⟨hz, u, uz.symm⟩
  by_cases hx : x ∈ live G
  · calc
      _ = ∑ u ∈ G.neighborFinset x, (branch G x u).card :=
        Finset.sum_congr rfl (fun u hu => (sizes u hu).symm)
      _ = ((G.neighborFinset x).biUnion (branch G x)).card := (Finset.card_biUnion disj).symm
      _ ≤ ((live G).erase x).card := Finset.card_le_card contained
      _ = _ := Finset.card_erase_of_mem hx
  · have empty : G.neighborFinset x = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, (G.mem_neighborFinset _ _).mp hu⟩)
    simp [empty]

theorem square_sum_bound
    (rows : ∀ x, ∑ u ∈ G.neighborFinset x, G.degree u ≤ (live G).card - 1) :
    ∑ u ∈ live G, (G.degree u)^2 ≤ (live G).card * ((live G).card - 1) := by
  classical
  have rowsum (x : Fin n) : ∑ u ∈ live G, (if G.Adj x u then G.degree u else 0) =
      ∑ u ∈ G.neighborFinset x, G.degree u := by
    rw [← Finset.sum_filter, filtered_neighbors]
  have colsum (u : Fin n) : ∑ x ∈ live G, (if G.Adj x u then G.degree u else 0) =
      (G.degree u)^2 := by
    calc
      _ = ∑ x ∈ live G, (if G.Adj u x then G.degree u else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases h : G.Adj x u
        · simp [h, h.symm]
        · have h' : ¬ G.Adj u x := fun k => h k.symm
          simp [h, h']
      _ = _ := by
        rw [← Finset.sum_filter, filtered_neighbors]
        simp [pow_two]
  calc
    _ = ∑ u ∈ live G, ∑ x ∈ live G, (if G.Adj x u then G.degree u else 0) :=
       Finset.sum_congr rfl (fun u _ => (colsum u).symm)
    _ = ∑ x ∈ live G, ∑ u ∈ live G, (if G.Adj x u then G.degree u else 0) := Finset.sum_comm
    _ ≤ ∑ _x ∈ live G, ((live G).card - 1) := Finset.sum_le_sum (fun x _ => (rowsum x).trans_le (rows x))
    _ = _ := by simp

theorem edge_envelope
    (rows : ∀ x, ∑ u ∈ G.neighborFinset x, G.degree u ≤ (live G).card - 1) :
    (2 * G.edgeFinset.card)^2 ≤ (live G).card^2 * ((live G).card - 1) := by
  classical
  have degrees : ∑ u ∈ live G, G.degree u = ∑ u, G.degree u := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro u _ hu
    have none : ¬ ∃ w, G.Adj u w := by simpa [live] using hu
    exact Nat.eq_zero_of_not_pos (fun h => none ((G.degree_pos_iff_exists_adj u).mp h))
  rw [← G.sum_degrees_eq_twice_card_edges, ← degrees]
  calc
    _ ≤ (live G).card * ∑ u ∈ live G, (G.degree u)^2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq (live G) (fun _ => (1 : ℕ)) (fun u => G.degree u)
    _ ≤ (live G).card * ((live G).card * ((live G).card - 1)) :=
      Nat.mul_le_mul_left _ (square_sum_bound G rows)
    _ = _ := by ring

theorem ratio_threshold {v e s c : ℕ} (support : v ≤ s + 1)
    (envelope : (2*e)^2 ≤ v^2 * (v-1)) (beat : c*(s+1) < e) :
    4*c^2 + 2 ≤ v ∧ 4*c^2 + 1 ≤ s := by
  have h : c*v < e := (Nat.mul_le_mul_left _ support).trans_lt beat
  have hsq : (2*(c*v))^2 < (2*e)^2 := by gcongr
  have step : v^2 * (4*c^2) < v^2 * (v-1) := by
    calc
      _ = (2*(c*v))^2 := by ring
      _ < _ := hsq.trans_le envelope
  have strict : 4*c^2 < v-1 := Nat.lt_of_mul_lt_mul_left step
  omega

end GirthFiveCounting

namespace InducedPath4

variable {n : ℕ} {G : SimpleGraph (Fin n)}

def extend (e : Fin 4 ↪ Fin n) (x : Fin 4 → Bool) (v : Fin n) : Bool :=
  decide (∃ i, e i = v ∧ x i = true)

theorem extend_apply (e : Fin 4 ↪ Fin n) (x : Fin 4 → Bool) (i : Fin 4) :
    extend e x (e i) = x i := by
  simp [extend]

theorem extend_off (e : Fin 4 ↪ Fin n) (x : Fin 4 → Bool) {v : Fin n}
    (outside : ∀ i, e i ≠ v) : extend e x v = false := by
  simp [extend, outside]

theorem from_cycle
    (girth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    {v : Fin n} {p : G.Walk v v} (cycle : p.IsCycle) :
    ∃ e : Fin 4 ↪ Fin n, ∀ i j : Fin 4,
      G.Adj (e i) (e j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  have len := girth v p cycle
  let e : Fin 4 ↪ Fin n := ⟨fun i => p.getVert i.val, by
    intro i j same
    apply Fin.ext
    exact cycle.getVert_injOn' (by change i.val ≤ p.length - 1; omega)
      (by change j.val ≤ p.length - 1; omega) same⟩
  have ab : G.Adj (e 0) (e 1) := p.adj_getVert_succ (i := 0) (by omega)
  have bc : G.Adj (e 1) (e 2) := p.adj_getVert_succ (i := 1) (by omega)
  have cd : G.Adj (e 2) (e 3) := p.adj_getVert_succ (i := 2) (by omega)
  have ac := NeighborhoodGirth.two_step_nonadj girth ab bc
  have bd := NeighborhoodGirth.two_step_nonadj girth bc cd
  have ad : ¬ G.Adj (e 0) (e 3) := by
    intro chord
    have eq := NeighborhoodGirth.common_neighbor_eq girth ab chord (e.injective.ne (by decide)) bc cd.symm
    exact (e.injective.ne (by decide : (2 : Fin 4) ≠ 0)) eq
  have ca : ¬ G.Adj (e 2) (e 0) := fun h => ac h.symm
  have db : ¬ G.Adj (e 3) (e 1) := fun h => bd h.symm
  have da : ¬ G.Adj (e 3) (e 0) := fun h => ad h.symm
  refine ⟨e, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [ab,bc,cd,ab.symm,bc.symm,cd.symm,ac,bd,ad,ca,db,da]

theorem from_not_acyclic
    (girth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (hasCycle : ¬ ∀ (v : Fin n) (p : G.Walk v v), ¬ p.IsCycle) :
    ∃ e : Fin 4 ↪ Fin n, ∀ i j : Fin 4,
      G.Adj (e i) (e j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  by_contra none
  exact hasCycle (fun _ _ cycle => none (from_cycle girth cycle))

theorem restrict_circuit [DecidableRel G.Adj] {D : PEqualNP.CircuitLowerBounds.Circuit}
    (computes : PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool =>
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)))
    (e : Fin 4 ↪ Fin n) (induced : ∀ i j : Fin 4,
      G.Adj (e i) (e j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val)
    (x : Fin 4 → Bool) : PEqualNP.MetaComplexity.circuitFun n D (extend e x) =
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)) := by
  rw [computes]
  have transport : (∃ i j, G.Adj i j ∧ extend e x i = true ∧ extend e x j = true) ↔
      ∃ i j : Fin 4, (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ x i = true ∧ x j = true := by
    constructor
    · rintro ⟨u,v,adj,hu,hv⟩
      obtain ⟨i,rfl,hi⟩ := of_decide_eq_true hu
      obtain ⟨j,rfl,hj⟩ := of_decide_eq_true hv
      exact ⟨i,j,(induced i j).mp adj,hi,hj⟩
    · rintro ⟨i,j,adj,hi,hj⟩
      exact ⟨e i,e j,(induced i j).mpr adj, (extend_apply e x i).trans hi,
        (extend_apply e x j).trans hj⟩
  simp only [transport]
  exact path_formula x
where
  path_formula : ∀ y : Fin 4 → Bool,
      decide (∃ i j : Fin 4, (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ y i = true ∧ y j = true)
        = ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3)) := by decide +kernel

end InducedPath4

/-! The edge function of the four-vertex path has no nontrivial AND/OR decomposition
on disjoint blocks of input coordinates. -/
namespace ReadOnceP4

abbrev Input := Fin 4 → Bool

def path (x : Input) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)

def mix (m x y : Input) : Input := fun i => if m i then x i else y i

def OnBlock (m : Input) (f : Input → Bool) : Prop :=
  ∀ x y : Input, (∀ i, m i = true → x i = y i) → f x = f y

/-- Every proper split admits two rejecting inputs whose mix accepts and two accepting
inputs whose mix rejects. This is a finite statement about the 16 inputs of the path. -/
theorem mixed_witnesses : ∀ m : Input, (∃ i, m i = true) → (∃ j, m j = false) →
    (∃ x y, path x = false ∧ path y = false ∧ path (mix m x y) = true) ∧
    (∃ x y, path x = true ∧ path y = true ∧ path (mix m x y) = false) := by
  decide +kernel

/-- Neither Boolean operation at the root can compute the path from disjoint nonempty blocks. -/
theorem no_root_split (m : Input) (yes : ∃ i, m i = true) (no : ∃ j, m j = false)
    (f g : Input → Bool) (hf : OnBlock m f) (hg : OnBlock (fun i => !(m i)) g) :
    (¬ ∀ x, path x = (f x || g x)) ∧ (¬ ∀ x, path x = (f x && g x)) := by
  have left (x y : Input) : f (mix m x y) = f x :=
    hf _ _ (fun i h => by simp [mix, h])
  have right (x y : Input) : g (mix m x y) = g y := by
    apply hg
    intro i hi
    have h : m i = false := by simpa using hi
    simp [mix, h]
  obtain ⟨⟨x,y,fx,fy,mxy⟩,⟨u,v,fu,fv,muv⟩⟩ := mixed_witnesses m yes no
  constructor
  · intro rep
    rw [rep, left, right] at mxy
    rw [rep] at fx fy
    cases f x <;> cases g x <;> cases f y <;> cases g y <;> simp_all
  · intro rep
    rw [rep, left, right] at muv
    rw [rep] at fu fv
    cases f u <;> cases g u <;> cases f v <;> cases g v <;> simp_all

inductive Expr where
  | var (i : Fin 4)
  | const (b : Bool)
  | gate (isAnd : Bool) (left right : Expr)

def join (isAnd x y : Bool) : Bool := if isAnd then x && y else x || y

def Expr.eval : Expr → Input → Bool
  | .var i, x => x i
  | .const b, _ => b
  | .gate op l r, x => join op (l.eval x) (r.eval x)

def Expr.vars : Expr → Finset (Fin 4)
  | .var i => {i}
  | .const _ => ∅
  | .gate _ l r => l.vars ∪ r.vars

def Expr.readOnce : Expr → Prop
  | .var _ | .const _ => True
  | .gate _ l r => l.readOnce ∧ r.readOnce ∧ Disjoint l.vars r.vars

private theorem eval_agrees (e : Expr) (x y : Input) (h : ∀ i ∈ e.vars, x i = y i) :
    e.eval x = e.eval y := by
  induction e with
  | var i => apply h; simp [Expr.vars]
  | const => rfl
  | gate op l r ih jh =>
    change join op (l.eval x) (r.eval x) = join op (l.eval y) (r.eval y)
    rw [ih (fun i hi => h i (Finset.mem_union_left _ hi)),
      jh (fun i hi => h i (Finset.mem_union_right _ hi))]

private theorem no_constant : ∀ b : Bool, ¬∀ x, path x = b := by decide +kernel
private theorem no_variable : ∀ i : Fin 4, ¬∀ x, path x = x i := by decide +kernel

private theorem constant_left (op b : Bool) (q : Input → Bool) (other : ¬∀ x, path x = q x) :
    ¬∀ x, path x = join op b (q x) := by
  cases op <;> cases b <;> simp [join, other, no_constant]

/-- The path admits no read-once monotone formula, including formulas with constants. -/
theorem no_read_once (e : Expr) (once : e.readOnce) : ¬∀ x, path x = e.eval x := by
  induction e with
  | var i => exact no_variable i
  | const b => exact no_constant b
  | gate op l r ih jh =>
    obtain ⟨lo,ro,disj⟩ := once
    by_cases lne : l.vars.Nonempty
    · by_cases rne : r.vars.Nonempty
      · let m : Input := fun i => decide (i ∈ l.vars)
        obtain ⟨i,hi⟩ := lne
        obtain ⟨j,hj⟩ := rne
        have away (k) (hk : k ∈ r.vars) : k ∉ l.vars := fun h => Finset.disjoint_left.mp disj h hk
        have split := no_root_split m ⟨i, by simp [m,hi]⟩ ⟨j, by simp [m,away j hj]⟩ l.eval r.eval
          (fun x y eq => eval_agrees l x y (fun k hk => eq k (by simp [m,hk])))
          (fun x y eq => eval_agrees r x y (fun k hk => eq k (by simp [m,away k hk])))
        cases op
        · exact split.1
        · exact split.2
      · have hr (x : Input) : r.eval x = r.eval (fun _ => false) :=
          eval_agrees r _ _ (fun k hk => False.elim (rne ⟨k,hk⟩))
        intro rep
        apply constant_left op (r.eval (fun _ => false)) l.eval (ih lo)
        intro x
        have h := rep x
        change path x = join op (l.eval x) (r.eval x) at h
        rw [hr x] at h
        cases op <;> simpa [join,Bool.and_comm,Bool.or_comm] using h
    · have hl (x : Input) : l.eval x = l.eval (fun _ => false) :=
        eval_agrees l _ _ (fun k hk => False.elim (lne ⟨k,hk⟩))
      intro rep
      apply constant_left op (l.eval (fun _ => false)) r.eval (jh ro)
      intro x
      have h := rep x
      change path x = join op (l.eval x) (r.eval x) at h
      rwa [hl x] at h

end ReadOnceP4

/-! Equality in the output-support bound forces each gate to merge two fresh branches. -/
namespace ReadOnceCircuit
open GraphCircuitSupport ReadOnceP4 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def predSet (s : Finset ℕ) (m : ℕ) (g : Gate) :=
  if m ∈ s then s.erase m ∪ g.inputs.toFinset else s

private theorem pred_le (s : Finset ℕ) (m : ℕ) (g : Gate) (fan : g.inputs.length ≤ 2) :
    (predSet s m g).card ≤ s.card + 1 := by
  unfold predSet
  split_ifs with h
  · have := Finset.card_erase_add_one h
    have := Finset.card_union_le (s.erase m) g.inputs.toFinset
    have := List.toFinset_card_le g.inputs
    omega
  · omega

private theorem two_fresh (s : Finset ℕ) (m : ℕ) (g : Gate) (fan : g.inputs.length ≤ 2)
    (tight : (predSet s m g).card = s.card + 1) :
    m ∈ s ∧ ∃ i j, g.inputs = [i,j] ∧ i ≠ j ∧ i ∉ s.erase m ∧ j ∉ s.erase m := by
  have hm : m ∈ s := by
    by_contra hn
    simp [predSet,hn] at tight
  have er := Finset.card_erase_add_one hm
  have un := Finset.card_union_le (s.erase m) g.inputs.toFinset
  have tc := List.toFinset_card_le g.inputs
  rw [predSet, ite_eq_left hm] at tight
  have dis := Finset.card_union_eq_card_add_card.mp (show (s.erase m ∪ g.inputs.toFinset).card = (s.erase m).card + g.inputs.toFinset.card by omega)
  have tc2 : g.inputs.toFinset.card = 2 := by omega
  have gl2 : g.inputs.length = 2 := by omega
  have pair : ∀ a : List ℕ, a.length = 2 → ∃ i j, a = [i,j] := by
    intro a a2
    cases a with
    | nil => simp at a2
    | cons i t =>
      cases t with
      | nil => simp at a2
      | cons j rest =>
        have h : rest = [] := by simpa using a2
        exact ⟨i,j,by rw [h]⟩
  obtain ⟨i,j,hij⟩ := pair g.inputs gl2
  rw [hij] at tc2 dis
  refine ⟨hm,i,j,hij,?_,?_,?_⟩
  · rintro rfl; simp at tc2
  · exact fun h => Finset.disjoint_left.mp dis h (by simp)
  · exact fun h => Finset.disjoint_left.mp dis h (by simp)

private structure Good (e : ℕ → Expr) (s : Finset ℕ) : Prop where
  once : ∀ i ∈ s, (e i).readOnce
  apart : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (e i).vars (e j).vars

private theorem good_gate (e : ℕ → Expr) (s : Finset ℕ) (m i j : ℕ) (op : Bool)
    (diff : i ≠ j) (hi : i ∉ s.erase m) (hj : j ∉ s.erase m)
    (old : Good e (s.erase m ∪ {i,j})) :
    Good (Function.update e m (.gate op (e i) (e j))) s := by
  have oi : i ∈ s.erase m ∪ {i,j} := by simp
  have oj : j ∈ s.erase m ∪ {i,j} := by simp
  have rest (k) (hk : k ∈ s) (hm : k ≠ m) : k ∈ s.erase m := Finset.mem_erase.mpr ⟨hm,hk⟩
  have gate_sep (k) (hk : k ∈ s.erase m) : Disjoint ((e i).vars ∪ (e j).vars) (e k).vars := by
    apply Finset.disjoint_union_left.mpr
    have ok : k ∈ s.erase m ∪ {i,j} := Finset.mem_union_left _ hk
    exact ⟨old.apart i oi k ok (fun h => hi (h ▸ hk)), old.apart j oj k ok (fun h => hj (h ▸ hk))⟩
  constructor
  · intro k hk
    by_cases q : k = m
    · subst k
      simp only [Function.update_self,Expr.readOnce]
      exact ⟨old.once i oi,old.once j oj,old.apart i oi j oj diff⟩
    · rw [Function.update_of_ne q]
      exact old.once k (Finset.mem_union_left _ (rest k hk q))
  · intro k hk l hl kl
    by_cases q : k = m
    · subst k
      rw [Function.update_self,Function.update_of_ne (Ne.symm kl)]
      exact gate_sep l (rest l hl (Ne.symm kl))
    · rw [Function.update_of_ne q]
      by_cases t : l = m
      · subst l
        rw [Function.update_self]
        exact (gate_sep k (rest k hk q)).symm
      · rw [Function.update_of_ne t]
        exact old.apart k (Finset.mem_union_left _ (rest k hk q)) l (Finset.mem_union_left _ (rest l hl t)) kl

private theorem old_wire (w : List Bool) (g : Gate) (i : ℕ) (ne : i ≠ w.length) :
    (gateStep w g).getD i false = w.getD i false := by
  by_cases lt : i < w.length
  · simp only [gateStep,List.getD_eq_getElem?_getD,List.getElem?_append_left lt]
  · have short : (gateStep w g).length ≤ i := by simp [gateStep]; omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none short,List.getElem?_eq_none (by omega : w.length ≤ i)]

private theorem new_wire (w : List Bool) (g : Gate) :
    (gateStep w g).getD w.length false = g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
  simp [gateStep,List.getD_eq_getElem?_getD]

private theorem build (gs : List Gate) (m : ℕ) (out : Finset ℕ) (w : Input → List Bool)
    (len : ∀ x, (w x).length = m) (mono : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (tight : (needed gs m out).card = out.card + gs.length)
    (e : ℕ → Expr) (good : Good e (needed gs m out))
    (fits : ∀ i ∈ needed gs m out, ∀ x, (w x).getD i false = (e i).eval x) :
    ∃ e' : ℕ → Expr, Good e' out ∧ ∀ i ∈ out, ∀ x, (gs.foldl gateStep (w x)).getD i false = (e' i).eval x := by
  classical
  induction gs generalizing m w e with
  | nil => exact ⟨e,good,fits⟩
  | cons g gs ih =>
    let s := needed gs (m+1) out
    have spec := mono g (by simp)
    have tail := fun z hz => mono z (List.mem_cons_of_mem g hz)
    have h1 := pred_le s m g spec.2
    have h2 : s.card ≤ out.card + gs.length := needed_card gs (m+1) out (fun z hz => (tail z hz).2)
    change (predSet s m g).card = out.card + (g :: gs).length at tight
    simp only [List.length_cons] at tight
    have localEq : (predSet s m g).card = s.card + 1 := by omega
    have suffixEq : s.card = out.card + gs.length := by omega
    obtain ⟨hm,i,j,ins,ij,hi,hj⟩ := two_fresh s m g spec.2 localEq
    have pre : needed (g :: gs) m out = s.erase m ∪ {i,j} := by
      change predSet s m g = _
      simp [predSet,hm,ins]
    rw [pre] at good fits
    let op := decide (g.op = GateOp.and)
    let label := Function.update e m (.gate op (e i) (e j))
    apply ih (m+1) (fun x => gateStep (w x) g) (by intro x; simp [gateStep,len]) tail suffixEq label
      (good_gate e s m i j op ij hi hj good)
    intro k hk x
    by_cases eq : k = m
    · subst k
      rw [← len x, new_wire, len x]
      have fi := fits i (by simp) x
      have fj := fits j (by simp) x
      simp only [List.getD_eq_getElem?_getD] at fi fj
      have kinds : g.op = GateOp.and ∨ g.op = GateOp.or := spec.1
      rcases kinds with ha | ho
      · simp [label,Function.update_self,Expr.eval,op,join,ins,ha,GateOp.eval,fi,fj]
      · simp [label,Function.update_self,Expr.eval,op,join,ins,ho,GateOp.eval,fi,fj]
    · rw [old_wire _ _ _ (by simpa [len] using eq)]
      rw [show label k = e k from Function.update_of_ne eq _ _]
      exact fits k (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hk⟩)) x


private noncomputable def inputLabel {n : ℕ} (κ : Fin 4 ↪ Fin n) (k : ℕ) : Expr :=
  if h : ∃ i, (κ i).val = k then .var (Classical.choose h) else .const false

private theorem input_good {n : ℕ} (κ : Fin 4 ↪ Fin n) (s : Finset ℕ) : Good (inputLabel κ) s := by
  classical
  constructor
  · intro i _
    unfold inputLabel
    split <;> trivial
  · intro i _ j _ ne
    unfold inputLabel
    split <;> split
    case isTrue.isTrue h k =>
      have diff : Classical.choose h ≠ Classical.choose k := by
        intro eq
        exact ne ((Classical.choose_spec h).symm.trans ((congrArg (fun t => (κ t).val) eq).trans (Classical.choose_spec k)))
      simp [Expr.vars,diff]
    all_goals simp [Expr.vars]

private theorem input_fits {n : ℕ} (κ : Fin 4 ↪ Fin n) (k : ℕ) (x : Input) :
    (List.ofFn (InducedPath4.extend κ x)).getD k false = (inputLabel κ k).eval x := by
  classical
  unfold inputLabel
  split
  next h =>
    have eq := Classical.choose_spec h
    calc
      (List.ofFn (InducedPath4.extend κ x)).getD k false =
          (List.ofFn (InducedPath4.extend κ x)).getD (κ (Classical.choose h)).val false :=
        congrArg (fun a => (List.ofFn (InducedPath4.extend κ x)).getD a false) eq.symm
      _ = InducedPath4.extend κ x (κ (Classical.choose h)) := by simp [List.getD_eq_getElem?_getD]
      _ = _ := InducedPath4.extend_apply κ x _
  next h =>
    by_cases valid : k < n
    · have none : ¬∃ t, κ t = ⟨k,valid⟩ ∧ x t = true := by
        rintro ⟨t,ht,_⟩
        exact h ⟨t,congrArg Fin.val ht⟩
      simp [List.getD_eq_getElem?_getD,valid,Expr.eval,InducedPath4.extend,none]
    · simp [List.getD_eq_getElem?_getD,valid,Expr.eval]

/-- A four-coordinate restriction equal to the path edge function excludes equality in
    the support bound. -/
theorem strict_support {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit)
    (mono : Monotone2 D) (computes : circuitFun n D = edge G) (κ : Fin 4 ↪ Fin n)
    (restrict : ∀ x, circuitFun n D (InducedPath4.extend κ x) = path x) : (active G).card ≤ D.size := by
  classical
  by_contra! strict
  have lower := Finset.card_le_card (active_subset G D computes)
  rw [Finset.card_image_of_injective _ Fin.val_injective] at lower
  have upper := needed_card D.gates n {D.output} (fun g hg => (mono g hg).2)
  have tight : (needed D.gates n {D.output}).card = ({D.output} : Finset ℕ).card + D.gates.length := by
    simp only [Finset.card_singleton] at upper ⊢
    change D.gates.length < _ at strict
    omega
  obtain ⟨e,good,fits⟩ := build D.gates n {D.output} (fun x => List.ofFn (InducedPath4.extend κ x))
    (by simp) mono tight (inputLabel κ) (input_good κ _) (fun i _ x => input_fits κ i x)
  exact no_read_once _ (good.once D.output (by simp)) (fun x => (restrict x).symm.trans (fits D.output (by simp) x))

/-- For girth at least five, the presence of a cycle costs one extra gate beyond
    the ordinary support lower bound. -/
theorem cyclic_support {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit)
    (girth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    {v : Fin n} {p : G.Walk v v} (cycle : p.IsCycle)
    (mono : Monotone2 D) (computes : circuitFun n D = edge G) : (active G).card ≤ D.size := by
  obtain ⟨κ, induced⟩ := InducedPath4.from_cycle girth cycle
  exact strict_support G D mono computes κ (InducedPath4.restrict_circuit computes κ induced)

end ReadOnceCircuit

namespace GirthFiveCounting

theorem strict_ratio_threshold {v e s c : ℕ} (positive : 1 ≤ c) (support : v ≤ s)
    (envelope : (2*e)^2 ≤ v^2 * (v-1)) (beat : c*(s+1) < e) :
    4*c^2 + 4 ≤ v ∧ 4*c^2 + 4 ≤ s := by
  suffices cut : 4*c^2+4 ≤ v from ⟨cut, cut.trans support⟩
  by_contra! small
  have h := (Nat.mul_le_mul_left c (Nat.succ_le_succ support)).trans_lt beat
  have lower : c*v+c+1 ≤ e := by rw [Nat.mul_succ] at h; omega
  have psq : (2*(c*v+c+1))^2 ≤ (2*e)^2 := by gcongr
  have vmax : v - 1 ≤ 4*c^2+2 := by omega
  have upper := Nat.mul_le_mul_left (v^2) vmax
  have coeff : 2*v ≤ 8*c*(c+1) := by nlinarith only [small, positive]
  have scaled := Nat.mul_le_mul_right v coeff
  nlinarith only [psq, envelope, upper, scaled, Nat.zero_le (c^2), Nat.zero_le c]

end GirthFiveCounting

namespace ForestSupport

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

theorem acyclic_edges_le_active (forest : G.IsAcyclic) :
    G.edgeFinset.card ≤ (GraphCircuitSupport.active G).card := by
  classical
  let H := G.induce G.support
  have count := (forest.induce G.support).ncard_edgeSet_add_card_connectedComponent
  have support_eq : (GraphCircuitSupport.active G : Set (Fin n)) = G.support := by
    ext v
    simp [GraphCircuitSupport.active, SimpleGraph.mem_support]
  have vertices : Nat.card G.support = (GraphCircuitSupport.active G).card := by
    rw [Nat.card_coe_set_eq, ← support_eq, Set.ncard_coe_finset]
  have edges : H.edgeSet.ncard = G.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    exact G.card_edgeFinset_induce_support
  change H.edgeSet.ncard + Nat.card H.ConnectedComponent = Nat.card G.support at count
  omega

theorem cycle_of_active_lt_edges (excess : (GraphCircuitSupport.active G).card < G.edgeFinset.card) :
    ∃ v, ∃ p : G.Walk v v, p.IsCycle := by
  apply SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp
  exact fun forest => (not_le_of_gt excess) (acyclic_edges_le_active forest)

end ForestSupport
namespace GirthFiveCounting
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
/-- Applied to precisely the graph, circuit and strict inequality of a prospective witness. -/
theorem witness_requirements {c n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (girth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (D : Circuit) (mono : Monotone2 D)
    (computes : circuitFun n D =
      fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true))
    (beat : c * (D.size + 1) < G.edgeFinset.card) :
    4*c^2 + 2 ≤ (live G).card ∧ 4*c^2 + 1 ≤ D.size ∧ ∃ v, 2*c < G.degree v := by
  have support : (live G).card ≤ D.size + 1 :=
    GraphCircuitSupport.active_bound G D (fun g hg => (mono g hg).2) computes
  have rows := row_bound G (NeighborhoodGirth.two_step_nonadj girth)
    (NeighborhoodGirth.common_neighbor_eq girth)
  obtain ⟨vertices, gates⟩ := ratio_threshold support (edge_envelope G rows) beat
  exact ⟨vertices, gates, GraphCircuitSupport.high_degree_required G D mono computes beat⟩



/-- Once the graph contains a cycle, saturation of the ordinary support bound is impossible. -/
theorem cyclic_witness_threshold {c n : ℕ} (positive : 1 ≤ c)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (girth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (D : Circuit) (mono : Monotone2 D) (computes : circuitFun n D = GraphCircuitSupport.edge G)
    {x : Fin n} {p : G.Walk x x} (cyc : p.IsCycle)
    (beat : c * (D.size + 1) < G.edgeFinset.card) :
    4*c^2 + 4 ≤ (live G).card ∧ 4*c^2 + 4 ≤ D.size := by
  have rows := row_bound G (NeighborhoodGirth.two_step_nonadj girth)
    (NeighborhoodGirth.common_neighbor_eq girth)
  exact strict_ratio_threshold positive (ReadOnceCircuit.cyclic_support G D girth cyc mono computes)
    (edge_envelope G rows) beat


/-- At a positive factor, a violating graph must already contain a cycle. -/
theorem positive_witness_threshold {c n : ℕ} (positive : 1 ≤ c)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (girth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (D : Circuit) (mono : Monotone2 D) (computes : circuitFun n D = GraphCircuitSupport.edge G)
    (beat : c * (D.size + 1) < G.edgeFinset.card) :
    4*c^2 + 4 ≤ (live G).card ∧ 4*c^2 + 4 ≤ D.size := by
  have s := GraphCircuitSupport.active_bound G D (fun g hg => (mono g hg).2) computes
  have le := Nat.mul_le_mul_right (D.size+1) positive
  rw [Nat.one_mul] at le
  obtain ⟨x,p,cyc⟩ := ForestSupport.cycle_of_active_lt_edges (s.trans_lt (le.trans_lt beat))
  exact cyclic_witness_threshold positive G girth D mono computes cyc beat

end GirthFiveCounting
