import PEqualNP.Defs.MetaComplexityLgpMono

namespace CubeEdgeUpper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or,[7,4]⟩, ⟨.or,[2,1]⟩, ⟨.or,[4,9]⟩, ⟨.and,[0,10]⟩,
    ⟨.or,[7,9]⟩, ⟨.and,[3,12]⟩, ⟨.or,[1,8]⟩, ⟨.and,[5,14]⟩,
    ⟨.or,[2,8]⟩, ⟨.and,[6,16]⟩, ⟨.or,[11,13]⟩, ⟨.or,[15,17]⟩,
    ⟨.or,[18,19]⟩], 20⟩

private theorem monotone : Monotone2 circuit := by
  intro g hg
  simp [circuit] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst g <;> simp [Set.mem_insert_iff, Set.mem_singleton_iff]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem evalList : ∀ a b c d e f g h : Bool,
    circuit.eval [a,b,c,d,e,f,g,h] =
      ((a && b) || (a && c) || (a && e) || (b && d) || (b && f) ||
       (c && d) || (c && g) || (d && h) || (e && f) || (e && g) ||
       (f && h) || (g && h)) := by decide

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

theorem thirteen_gates_suffice :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 13 ∧
      (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 8, (u.val, v.val) ∈
          ([(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),
            (4,5),(4,6),(5,7),(6,7)] : List (ℕ × ℕ)) ∧
          x u = true ∧ x v = true)) := by
  refine ⟨circuit, monotone, by decide, ?_⟩
  intro x
  have he : circuit.eval (List.ofFn x) = _ :=
    evalList (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  rw [he]
  simp (disch := decide) only [edgeCons, Bool.or_eq_true, Bool.and_eq_true,
    List.not_mem_nil, false_and, exists_false, or_false, or_assoc]
  rfl

end CubeEdgeUpper
