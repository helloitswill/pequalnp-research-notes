import PEqualNP.Defs

/-! Four-cycles obstruct two common graph products as witness families for L-meta-2029. -/
namespace ProductObstruction

open SimpleGraph

abbrev GirthFive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length

private theorem square {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (da : G.Adj d a)
    (ac : a ≠ c) (bd : b ≠ d) : ¬ GirthFive G := by
  let p : G.Walk a a := .cons ab (.cons bc (.cons cd (.cons da .nil)))
  have hc : p.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simp [p, Walk.isPath_def, bc.ne, bd, ab.ne.symm, cd.ne, ac.symm, da.ne]
    · change 3 ≤ 4
      decide
  intro hg
  have h := hg a p hc
  change 5 ≤ 4 at h
  omega

/-- In the direct (categorical) product, both coordinates move along an edge. -/
def directProduct {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V × W) where
  Adj x y := G.Adj x.1 y.1 ∧ H.Adj x.2 y.2
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _ h := h.1.ne rfl

/-- One vertex with two distinct neighbors in each factor forces a four-cycle. -/
theorem directProduct_not_girthFive {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {x u v : V} {y p q : W} (xu : G.Adj x u) (xv : G.Adj x v) (uv : u ≠ v)
    (yp : H.Adj y p) (yq : H.Adj y q) (pq : p ≠ q) :
    ¬ GirthFive (directProduct G H) := by
  apply square (a := (x,p)) (b := (u,y)) (c := (x,q)) (d := (v,y))
  · exact ⟨xu, yp.symm⟩
  · exact ⟨xu.symm, yq⟩
  · exact ⟨xv, yq.symm⟩
  · exact ⟨xv.symm, yp⟩
  · exact fun h => pq (congrArg Prod.snd h)
  · exact fun h => uv (congrArg Prod.fst h)

/-- The same square survives upon restricting to any shore product containing its four vertices. -/
theorem induced_directProduct_not_girthFive {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} {S : Set (V × W)}
    {x u v : V} {y p q : W} (xu : G.Adj x u) (xv : G.Adj x v) (uv : u ≠ v)
    (yp : H.Adj y p) (yq : H.Adj y q) (pq : p ≠ q)
    (xp : (x,p) ∈ S) (uy : (u,y) ∈ S) (xq : (x,q) ∈ S) (vy : (v,y) ∈ S) :
    ¬ GirthFive ((directProduct G H).induce S) := by
  apply square (a := ⟨(x,p),xp⟩) (b := ⟨(u,y),uy⟩) (c := ⟨(x,q),xq⟩) (d := ⟨(v,y),vy⟩)
  · exact ⟨xu, yp.symm⟩
  · exact ⟨xu.symm, yq⟩
  · exact ⟨xv, yq.symm⟩
  · exact ⟨xv.symm, yp⟩
  · exact fun h => pq (congrArg (fun z : S => z.val.2) h)
  · exact fun h => uv (congrArg (fun z : S => z.val.1) h)

/-- In the Cartesian product, one coordinate stays fixed while the other crosses an edge. -/
def cartesianProduct {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (V × W) where
  Adj x y := (G.Adj x.1 y.1 ∧ x.2 = y.2) ∨ (H.Adj x.2 y.2 ∧ x.1 = y.1)
  symm.symm _ _ := Or.imp (fun h => ⟨h.1.symm, h.2.symm⟩) (fun h => ⟨h.1.symm, h.2.symm⟩)
  loopless.irrefl _ h := h.elim (fun he => he.1.ne rfl) (fun he => he.1.ne rfl)

/-- In the Cartesian (box) product, one edge from each factor suffices. -/
theorem boxProd_not_girthFive {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {x u : V} {y p : W} (xu : G.Adj x u) (yp : H.Adj y p) :
    ¬ GirthFive (cartesianProduct G H) := by
  apply square (a := (x,y)) (b := (u,y)) (c := (u,p)) (d := (x,p))
  · exact Or.inl ⟨xu, rfl⟩
  · exact Or.inr ⟨yp, rfl⟩
  · exact Or.inl ⟨xu.symm, rfl⟩
  · exact Or.inr ⟨yp.symm, rfl⟩
  · exact fun h => xu.ne (congrArg Prod.fst h)
  · exact fun h => yp.ne (congrArg Prod.snd h)

/-- The obstruction persists under an injective relabeling, in particular onto a `Fin n`. -/
theorem not_girthFive_of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) (bad : ¬ GirthFive G) : ¬ GirthFive H := by
  intro hg
  apply bad
  intro v p hp
  simpa using hg (f v) (p.map f.toHom) (hp.map f.injective)

end ProductObstruction
