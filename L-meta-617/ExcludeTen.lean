import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import PEqualNP.Defs.MetaComplexityLgpMono
import PEqualNP.MetaComplexity.Helpers.ReadersExport
import PEqualNP.MetaComplexity.L106

/-!
# An eleven-gate lower bound for the edge predicate of the cube

For each cube vertex, fixing it to false leaves its antipode essential.
Fixing the antipode to false then leaves a six-cycle. The project’s fan-out
theorem saves at least two gates at the first restriction. One further reader
disappears at the second restriction. The six-cycle needs eight gates by L106.
-/

namespace Cube617

abbrev Input := Fin 8 → Bool
def cube (x : Input) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 4) || (x 1 && x 3) ||
  (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 6) || (x 3 && x 7) ||
  (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)

def atom (i : Fin 8) : Input := fun j => decide (i = j)
def onePin (u : Fin 8) (x : Input) : Bool := cube (Function.update x u false)
def opp (u : Fin 8) : Fin 8 := ⟨7-u.val, by omega⟩
def two (x : Input) (u : Fin 8) (a : Bool) (v : Fin 8) (b : Bool) : Input :=
  Function.update (Function.update x u a) v b

/-- A neighbor of vertex zero witnesses its dependence. -/
theorem cube_dep_zero :
    cube (Function.update (atom 1) 0 (!(atom 1 0))) ≠ cube (atom 1) := by decide

theorem cube_nc : ∀ (u : Fin 8) (b : Bool),
    cube (Function.update (fun _ => false) u b) ≠ cube (Function.update (fun _ => true) u b) := by
  decide

theorem sep_witness : ∀ (u v : Fin 8), u ≠ v → ∃ k : Fin 8,
    cube (two (atom k) u true v false) = true ∧
    cube (two (atom k) u false v true) = false ∧
    cube (two (atom k) u false v false) = false := by
  decide

theorem right_witness : ∀ (u v : Fin 8), u ≠ v → ∃ k : Fin 8,
    cube (two (atom k) u false v true) ≠ cube (two (atom k) u false v false) := by
  decide

theorem pin_dep : ∀ (u : Fin 8), ∃ k : Fin 8,
    onePin u (Function.update (atom k) (opp u) (!(atom k (opp u)))) ≠ onePin u (atom k) := by
  decide

theorem pin_nc : ∀ (u : Fin 8) (b : Bool),
    onePin u (Function.update (fun _ => false) (opp u) b) ≠
    onePin u (Function.update (fun _ => true) (opp u) b) := by decide

/-- Along the cycle at vertex zero, 1, 3, 2, 6, 4, 5 are positions zero through five. -/
def label (u i : Fin 8) : Fin 6 :=
  (![0, 0, 2, 1, 4, 5, 3, 0] : Fin 8 → Fin 6) (Fin.ofNat 8 (i.val ^^^ u.val))

def cycle6 (x : Fin 6 → Bool) : Bool :=
  decide (∃ i j : Fin 6, (i.val + 1) % 6 = j.val ∧ x i = true ∧ x j = true)

set_option maxRecDepth 250000 in
set_option maxHeartbeats 5000000 in
private theorem cycle_vec : ∀ (u : Fin 8) (a b c d e f : Bool),
    let x : Fin 6 → Bool := ![a,b,c,d,e,f]
    onePin u (Function.update (x ∘ label u) (opp u) false) = cycle6 x := by decide

theorem pin_cycle (u : Fin 8) (x : Fin 6 → Bool) :
    onePin u (Function.update (x ∘ label u) (opp u) false) = cycle6 x := by
  have hx : ![x 0, x 1, x 2, x 3, x 4, x 5] = x := by funext i; fin_cases i <;> rfl
  simpa only [hx] using cycle_vec u (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def edgeProp (x : Input) : Prop := ∃ u v : Fin 8, (u.val, v.val) ∈
    ([(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)] : List (ℕ × ℕ))
    ∧ x u = true ∧ x v = true

private theorem edgeCons (x : Fin 8 → Bool) (a b : ℕ) (es : List (ℕ × ℕ))
    (ha : a < 8) (hb : b < 8) :
    (∃ u v : Fin 8, (u.val, v.val) ∈ (a,b)::es ∧ x u = true ∧ x v = true) ↔
      (x ⟨a,ha⟩ = true ∧ x ⟨b,hb⟩ = true) ∨
      ∃ u v : Fin 8, (u.val, v.val) ∈ es ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u,v,h,hu,hv⟩
    rcases List.mem_cons.mp h with h | h
    · obtain ⟨h1,h2⟩ := Prod.mk.inj h
      exact Or.inl ⟨(show u = ⟨a,ha⟩ from Fin.ext h1) ▸ hu,
        (show v = ⟨b,hb⟩ from Fin.ext h2) ▸ hv⟩
    · exact Or.inr ⟨u,v,h,hu,hv⟩
  · rintro (⟨hu,hv⟩ | ⟨u,v,h,hu,hv⟩)
    · exact ⟨⟨a,ha⟩,⟨b,hb⟩,List.mem_cons_self,hu,hv⟩
    · exact ⟨u,v,List.mem_cons_of_mem _ h,hu,hv⟩

theorem cube_iff (x : Input) : cube x = true ↔ edgeProp x := by
  simp (disch := decide) only [cube, edgeProp, edgeCons, Bool.or_eq_true, Bool.and_eq_true,
    List.not_mem_nil, false_and, exists_false, or_false, or_assoc]
  rfl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.Readers
open PEqualNP.MetaComplexity.Helpers.PermInputs

private theorem cube_restr : RestrNC cube := by
  intro u _ b
  exact ⟨_, _, cube_nc u b⟩

private theorem cube_no_funnel : NoFunnel cube := by
  apply noFunnel_of_sep
  intro u v huv _ _
  obtain ⟨k, h10, h01, h00⟩ := sep_witness u v huv
  obtain ⟨j, hj⟩ := right_witness u v huv
  exact ⟨⟨atom k, by change cube (two (atom k) u true v false) ≠ _; rw [h10]; exact fun e => Bool.noConfusion (e.trans h00)⟩,
    ⟨atom j, hj⟩, ⟨atom k, by change cube (two (atom k) u true v false) ≠ _; rw [h10]; exact fun e => Bool.noConfusion (e.trans h01)⟩⟩

/-- On an essential input for which both restrictions are nonconstant, pinning saves a gate. -/
private theorem pin_saves_one {n : ℕ} (f : (Fin (n+1) → Bool) → Bool)
    (u : Fin (n+1)) (s : ℕ) (hd : Dep f u)
    (hn : ∀ b : Bool, ∃ x y : Fin (n+1) → Bool, f (Function.update x u b) ≠ f (Function.update y u b))
    (hc : HasCircuitSize (n+1) f s) : Drop f u false 1 s := by
  obtain ⟨gs, o, L, hlen⟩ := exists_least _ f s (dep_nc hd) hc
  obtain ⟨q, hq⟩ := L.dep_read u hd hn
  have h := L.save u false (hn false) {q} (by
    intro r hr
    have hr' := Finset.mem_singleton.mp hr
    subst r
    exact rc_input false hq)
  simpa only [Finset.card_singleton] using h.mono (le_refl _) hlen

/-- Even allowing NOT gates, a binary circuit for the edge predicate of the cube needs at least eleven gates. -/
theorem eleven_le (s : ℕ) (hc : HasCircuitSize 8 cube s) : 11 ≤ s := by
  obtain ⟨u, _, hp⟩ := fanout_step 7 cube s ⟨0, atom 1, cube_dep_zero⟩ cube_restr cube_no_funnel hc
  have h2 : Drop cube u false 2 s := by
    rcases hp with ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩
    · exact h.mono (by decide) le_rfl
    · exact h.mono (by decide) le_rfl
    · exact h
  obtain ⟨t, hts, ht⟩ := h2
  obtain ⟨k, hk⟩ := pin_dep u
  have hd : Dep (onePin u) (opp u) := ⟨atom k, hk⟩
  obtain ⟨r, hrt, hr⟩ := pin_saves_one (n := 7) (onePin u) (opp u) t hd (fun b => ⟨_,_,pin_nc u b⟩) ht
  have h6 := relabel_size (label u) _ r hr
  have he : (fun x : Fin 6 → Bool => onePin u (Function.update (x ∘ label u) (opp u) false)) = cycle6 :=
    funext (pin_cycle u)
  change HasCircuitSize 6 (fun x => onePin u (Function.update (x ∘ label u) (opp u) false)) r at h6
  rw [he] at h6
  have lower := (L106 6 r (by decide)).mp h6
  omega

theorem no_ten_gates :
    ¬ ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
      (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 8, (u.val, v.val) ∈
          ([(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),
            (4,5),(4,6),(5,7),(6,7)] : List (ℕ × ℕ)) ∧
          x u = true ∧ x v = true)) := by
  rintro ⟨C,hm,hs,he⟩
  have hf : FanInTwo C := by
    intro g hg
    obtain ⟨ho, hl⟩ := hm g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
    exact ⟨ho.imp_right Or.inl,hl⟩
  have hc : HasCircuitSize 8 cube 10 := by
    refine ⟨C,hf,hs,?_⟩
    intro x
    have e := (he x).trans (cube_iff x).symm
    simpa using e
  have h := eleven_le 10 hc
  omega

#print axioms eleven_le
#print axioms no_ten_gates
end Cube617
