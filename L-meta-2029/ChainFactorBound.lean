import PEqualNP.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import WitnessBound
import Mathlib.Order.Interval.Finset.Nat

namespace ChainCover

variable {U R I : Type*} [Fintype U] [DecidableEq U]

def hits (a s : Finset U) : Prop := ∃ x ∈ a, x ∈ s

def extent (columns : R → Finset U) (b : Finset R) : Finset U :=
  b.biUnion columns

theorem extent_exact_iff (N : Finset R → Finset U) (M : I → Finset R → Finset U)
    (extensive : ∀ i b, N b ⊆ M i b) :
    (∀ a b, hits a (N b) ↔ ∀ i, hits a (M i b)) ↔ ∀ b, ∃ i, M i b = N b := by
  classical
  constructor
  · intro correct b
    by_contra! all_strict
    let a := Finset.univ \ N b
    have each (i : I) : hits a (M i b) := by
      have nonsub : ¬ M i b ⊆ N b :=
        fun h => all_strict i (Finset.Subset.antisymm h (extensive i b))
      obtain ⟨x, hxM, hxN⟩ := Finset.not_subset.mp nonsub
      exact ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxN⟩, hxM⟩
    obtain ⟨x, hxa, hxN⟩ := (correct a b).2 each
    exact (Finset.mem_sdiff.mp hxa).2 hxN
  · intro tight a b
    constructor
    · rintro ⟨x, hxa, hxN⟩ i
      exact ⟨x, hxa, extensive i b hxN⟩
    · intro all
      obtain ⟨i, eq⟩ := tight b
      simpa [eq] using all i

theorem column_exact_iff (columns : R → Finset U) (large : I → R → Finset U)
    (extensive : ∀ i r, columns r ⊆ large i r) :
    (∀ a b, hits a (extent columns b) ↔ ∀ i, hits a (extent (large i) b)) ↔
      ∀ b, ∃ i, extent (large i) b = extent columns b := by
  apply extent_exact_iff
  intro i b x hx
  obtain ⟨r, hr, hxr⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨r, hr, extensive i r hxr⟩

/-- Complete a set to the union of the initial segments of its members.
Ranks can tie; an injective rank gives an ordinary total ordering. -/
def downClosure (rank : U → ℕ) (s : Finset U) : Finset U :=
  Finset.univ.filter (fun x => ∃ y ∈ s, rank x ≤ rank y)

omit [DecidableEq U] in
theorem prefix_contains (rank : U → ℕ) (s : Finset U) : s ⊆ downClosure rank s := by
  intro y hy
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hy, le_rfl⟩

theorem prefix_extent (rank : U → ℕ) (columns : R → Finset U) (b : Finset R) :
    extent (fun r => downClosure rank (columns r)) b = downClosure rank (extent columns b) := by
  ext x
  constructor
  · intro hx
    obtain ⟨r, hr, hxr⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨y, hyr, xy⟩ := (Finset.mem_filter.mp hxr).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, Finset.mem_biUnion.mpr ⟨r, hr, hyr⟩, xy⟩
  · intro hx
    obtain ⟨y, hy, xy⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨r, hr, hyr⟩ := Finset.mem_biUnion.mp hy
    exact Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hyr, xy⟩⟩

def IsInitial (rank : U → ℕ) (s : Finset U) : Prop :=
  ∀ x ∈ s, ∀ y, rank y ≤ rank x → y ∈ s

omit [DecidableEq U] in
theorem prefix_eq_iff (rank : U → ℕ) (s : Finset U) : downClosure rank s = s ↔ IsInitial rank s := by
  constructor
  · intro eq x hx y yx
    rw [← eq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, yx⟩
  · intro closed
    apply Finset.Subset.antisymm _ (prefix_contains rank s)
    intro y hy
    obtain ⟨x, hx, yx⟩ := (Finset.mem_filter.mp hy).2
    exact closed x hx y yx

theorem prefix_exact_iff (rank : I → U → ℕ) (columns : R → Finset U) :
    (∀ a b, hits a (extent columns b) ↔
      ∀ i, hits a (extent (fun r => downClosure (rank i) (columns r)) b)) ↔
    ∀ b, ∃ i, IsInitial (rank i) (extent columns b) := by
  rw [column_exact_iff columns _ (fun i r => prefix_contains (rank i) (columns r))]
  simp only [prefix_extent, prefix_eq_iff]

omit [Fintype U] in
theorem initial_comparable {rank : U → ℕ} {s t : Finset U}
    (hs : IsInitial rank s) (ht : IsInitial rank t) : s ⊆ t ∨ t ⊆ s := by
  classical
  by_cases h : s ⊆ t
  · exact Or.inl h
  · obtain ⟨x, hxs, hxt⟩ := Finset.not_subset.mp h
    apply Or.inr
    intro y hyt
    rcases le_total (rank y) (rank x) with yx | xy
    · exact hs x hxs y yx
    · exact False.elim (hxt (ht y hyt x xy))

theorem antichain_lower_bound {A : Type*} [Fintype A] [Fintype I]
    (rank : I → U → ℕ) (columns : R → Finset U) (family : A → Finset R)
    (incomp : ∀ a b, a ≠ b → ¬ extent columns (family a) ⊆ extent columns (family b))
    (correct : ∀ a b, hits a (extent columns b) ↔
      ∀ i, hits a (extent (fun r => downClosure (rank i) (columns r)) b)) :
    Fintype.card A ≤ Fintype.card I := by
  classical
  have covered := (prefix_exact_iff rank columns).1 correct
  choose label closed using fun a => covered (family a)
  apply Fintype.card_le_of_injective label
  intro a b eq
  by_contra ne
  have hb := closed b
  rw [← eq] at hb
  rcases initial_comparable (closed a) hb with ab | ba
  · exact incomp a b ne ab
  · exact incomp b a (Ne.symm ne) ba

end ChainCover

namespace ChainCover

variable {U R I : Type*} [Fintype U] [DecidableEq U] [Fintype R] [DecidableEq R]

def star (columns : R → Finset U) (x : U) : Finset R :=
  Finset.univ.filter (fun r => x ∈ columns r)

def avoiding (columns : R → Finset U) (X : Finset U) : Finset R :=
  Finset.univ.filter (fun r => Disjoint (columns r) X)

/-- Every sufficiently small omitted set is precisely the complement of a union of columns. -/
theorem small_complement (columns : R → Finset U) (d : ℕ)
    (degree : ∀ x, d ≤ (star columns x).card)
    (codegree : ∀ x y, x ≠ y → ((star columns x) ∩ (star columns y)).card ≤ 1)
    (X : Finset U) (small : X.card < d) :
    extent columns (avoiding columns X) = Finset.univ \ X := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨r, hr, hxr⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      Finset.disjoint_left.mp (Finset.mem_filter.mp hr).2 hxr⟩
  · intro hx
    have outside := (Finset.mem_sdiff.mp hx).2
    let bad := X.biUnion (fun y => (star columns x) ∩ (star columns y))
    have count : bad.card ≤ X.card := by
      calc
        _ ≤ ∑ y ∈ X, ((star columns x) ∩ (star columns y)).card := Finset.card_biUnion_le
        _ ≤ ∑ _y ∈ X, 1 := Finset.sum_le_sum (fun y hy =>
          codegree x y (fun eq => outside (eq.symm ▸ hy)))
        _ = X.card := by simp
    have escape : ¬ (star columns x) ⊆ bad := by
      intro contained
      exact (Nat.not_lt_of_ge (degree x)) ((Finset.card_le_card contained).trans_lt (count.trans_lt small))
    obtain ⟨r, hr, safe⟩ := Finset.not_subset.mp escape
    have disjoint : Disjoint (columns r) X := by
      apply Finset.disjoint_left.mpr
      intro y hyr hy
      exact safe (Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_inter.mpr
        ⟨hr, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyr⟩⟩⟩)
    exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, disjoint⟩,
      (Finset.mem_filter.mp hr).2⟩

/-- Prefix completions of all columns need at least one distinct order for each k-set,
when every point has degree greater than k and distinct points have codegree at most one. -/
theorem binomial_lower_bound [Fintype I] (rank : I → U → ℕ) (columns : R → Finset U)
    (d k : ℕ) (small : k < d) (degree : ∀ x, d ≤ (star columns x).card)
    (codegree : ∀ x y, x ≠ y → ((star columns x) ∩ (star columns y)).card ≤ 1)
    (correct : ∀ a b, hits a (extent columns b) ↔
      ∀ i, hits a (extent (fun r => downClosure (rank i) (columns r)) b)) :
    (Fintype.card U).choose k ≤ Fintype.card I := by
  classical
  let sets := (Finset.univ : Finset U).powersetCard k
  let fam := fun a : sets => avoiding columns a.val
  have card_eq (a : sets) : a.val.card = k := (Finset.mem_powersetCard.mp a.prop).2
  have ext_eq (a : sets) : extent columns (fam a) = Finset.univ \ a.val :=
    small_complement columns d degree codegree _ ((card_eq a).trans_lt small)
  have incomparable (a b : sets) (ne : a ≠ b) :
      ¬ extent columns (fam a) ⊆ extent columns (fam b) := by
    rw [ext_eq, ext_eq]
    intro sub
    have ba : b.val ⊆ a.val := by
      intro x hx
      by_contra outside
      exact (Finset.mem_sdiff.mp (sub (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, outside⟩))).2 hx
    have same : b.val = a.val := Finset.eq_of_subset_of_card_le ba (by rw [card_eq, card_eq])
    exact ne (Subtype.ext same.symm)
  have bound := antichain_lower_bound rank columns fam incomparable correct
  simpa [sets, Finset.card_powersetCard] using bound

end ChainCover

namespace ChainCover

variable {U R I : Type*} [Fintype U] [DecidableEq U] [DecidableEq R]

def restrictColumns (l : Finset U) (r : Finset R) (columns : R → Finset U) (y : r) :
    Finset l :=
  Finset.univ.filter (fun x : l => x.val ∈ columns y.val)

omit [Fintype U] in
theorem restrict_extent_mem (l : Finset U) (r : Finset R) (columns : R → Finset U)
    (b : Finset r) (x : l) :
    x ∈ extent (restrictColumns l r columns) b ↔ x.val ∈ extent columns (b.image Subtype.val) := by
  constructor
  · intro h
    obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.mp h
    exact Finset.mem_biUnion.mpr ⟨y.val, Finset.mem_image.mpr ⟨y, hy, rfl⟩,
      (Finset.mem_filter.mp hxy).2⟩
  · intro h
    obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.mp h
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩⟩

theorem restrict_exact (rank : I → U → ℕ) (columns : R → Finset U)
    (correct : ∀ a b, hits a (extent columns b) ↔
      ∀ i, hits a (extent (fun r => downClosure (rank i) (columns r)) b))
    (l : Finset U) (r : Finset R) :
    ∀ (a : Finset l) (b : Finset r), hits a (extent (restrictColumns l r columns) b) ↔
      ∀ i, hits a (extent (fun y => downClosure (fun x : l => rank i x.val)
        (restrictColumns l r columns y)) b) := by
  apply (prefix_exact_iff (fun i (x : l) => rank i x.val) (restrictColumns l r columns)).2
  intro b
  obtain ⟨i, closed⟩ := (prefix_exact_iff rank columns).1 correct (b.image Subtype.val)
  refine ⟨i, ?_⟩
  intro x hx y hy
  exact (restrict_extent_mem l r columns b y).2
    (closed x.val ((restrict_extent_mem l r columns b x).1 hx) y.val hy)

end ChainCover

namespace ChainCover

variable {U R I : Type*} [DecidableEq U] [Fintype R]

def missing (columns : R → Finset U) (x : U) : Finset R :=
  Finset.univ.filter (fun r => x ∉ columns r)

/-- Ordering the points by their number of missing columns makes every nested column initial. -/
theorem nested_initial (columns : R → Finset U)
    (nested : ∀ r t, columns r ⊆ columns t ∨ columns t ⊆ columns r) (r : R) :
    IsInitial (fun x => (missing columns x).card) (columns r) := by
  classical
  intro x hxr y order
  by_contra hyr
  have sub : missing columns x ⊆ missing columns y := by
    intro t ht
    have absent := (Finset.mem_filter.mp ht).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hyt
    rcases nested r t with rt | tr
    · exact absent (rt hxr)
    · exact hyr (tr hyt)
  have strict : missing columns x ⊂ missing columns y := by
    apply (Finset.ssubset_iff_of_subset sub).2
    exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyr⟩,
      fun h => (Finset.mem_filter.mp h).2 hxr⟩
  exact (Nat.not_lt_of_ge order) (Finset.card_lt_card strict)

/-- Any correct intersection of chain supergraphs can use the minimum column completions
under the same number of orders. -/
theorem nested_to_prefix [Fintype U] (columns : R → Finset U) (large : I → R → Finset U)
    (extensive : ∀ i r, columns r ⊆ large i r)
    (nested : ∀ i r t, large i r ⊆ large i t ∨ large i t ⊆ large i r)
    (correct : ∀ a b, hits a (extent columns b) ↔ ∀ i, hits a (extent (large i) b)) :
    ∃ rank : I → U → ℕ, ∀ a b, hits a (extent columns b) ↔
      ∀ i, hits a (extent (fun r => downClosure (rank i) (columns r)) b) := by
  let rank := fun i x => (missing (large i) x).card
  refine ⟨rank, (prefix_exact_iff rank columns).2 ?_⟩
  intro b
  obtain ⟨i, tight⟩ := (column_exact_iff columns large extensive).1 correct b
  refine ⟨i, ?_⟩
  rw [← tight]
  intro x hx y order
  obtain ⟨r, hr, hxr⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨r, hr, nested_initial (large i) (nested i) r x hxr y order⟩

end ChainCover

namespace PairBudget

variable {L R : Type*}

/-- No unordered pair of points can be counted in two different rows. -/
theorem pair_sum_le (ground : Finset L) (indices : Finset R) (row : R → Finset L)
    (inside : ∀ r ∈ indices, row r ⊆ ground)
    (unique : ∀ {r s}, r ∈ indices → s ∈ indices → r ≠ s →
      ∀ {a b}, a ∈ row r → a ∈ row s → b ∈ row r → b ∈ row s → a = b) :
    (∑ r ∈ indices, (row r).card.choose 2) ≤ ground.card.choose 2 := by
  classical
  have disj : (indices : Set R).PairwiseDisjoint (fun r => (row r).powersetCard 2) := by
    intro r hr s hs hrs
    rw [Function.onFun, Finset.disjoint_powersetCard_powersetCard]
    have bound : (row r ∩ row s).card ≤ 1 := by
      apply Finset.card_le_one_iff.mpr
      intro a b ha hb
      exact unique hr hs hrs (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp ha).2
        (Finset.mem_inter.mp hb).1 (Finset.mem_inter.mp hb).2
    omega
  have covered : (indices.biUnion fun r => (row r).powersetCard 2) ⊆ ground.powersetCard 2 := by
    intro p hp
    obtain ⟨r,hr,mem⟩ := Finset.mem_biUnion.mp hp
    exact Finset.powersetCard_mono (inside r hr) mem
  have count := Finset.card_le_card covered
  simpa [Finset.card_biUnion disj] using count

/-- Each row of size at least three has at least as many pairs as points. -/
theorem incidence_sum_le (ground : Finset L) (indices : Finset R) (row : R → Finset L)
    (inside : ∀ r ∈ indices, row r ⊆ ground)
    (unique : ∀ {r s}, r ∈ indices → s ∈ indices → r ≠ s →
      ∀ {a b}, a ∈ row r → a ∈ row s → b ∈ row r → b ∈ row s → a = b)
    (large : ∀ r ∈ indices, 3 ≤ (row r).card) :
    (∑ r ∈ indices, (row r).card) ≤ ground.card.choose 2 := by
  refine (Finset.sum_le_sum (g := fun r => (row r).card.choose 2) ?_).trans
    (pair_sum_le ground indices row inside unique)
  intro r hr
  have h := large r hr
  have mul := Nat.mul_le_mul_left (row r).card (show 2 ≤ (row r).card - 1 by omega)
  rw [Nat.choose_two_right]
  omega

/-- Restrict a global column incidence system to a finite choice of rows and columns. -/
theorem restricted_column_sum_le {U : Type*} [DecidableEq U] [Fintype R] [DecidableEq R]
    (columns : R → Finset U) (l : Finset U) (r : Finset R)
    (codegree : ∀ x z : U, x ≠ z →
      ((Finset.univ.filter fun y : R => x ∈ columns y) ∩
        (Finset.univ.filter fun y : R => z ∈ columns y)).card ≤ 1)
    (large : ∀ y ∈ r, 3 ≤ (l.filter fun x => x ∈ columns y).card) :
    (∑ y ∈ r, (l.filter fun x => x ∈ columns y).card) ≤ l.card.choose 2 := by
  apply incidence_sum_le l r (fun y => l.filter fun x => x ∈ columns y)
    (fun y _ => Finset.filter_subset _ _) _ large
  intro y w _ _ different a b ay aw by' bw
  by_contra unequal
  have both (t : R) (at' : a ∈ l.filter fun x => x ∈ columns t)
      (bt : b ∈ l.filter fun x => x ∈ columns t) :
      t ∈ (Finset.univ.filter fun v : R => a ∈ columns v) ∩
        (Finset.univ.filter fun v : R => b ∈ columns v) := by
    simp [(Finset.mem_filter.mp at').2, (Finset.mem_filter.mp bt).2]
  exact different (Finset.card_le_one_iff.mp (codegree a b unequal) (both y ay by') (both w aw bw))

end PairBudget

namespace CorePeeling

variable {U V : Type*} [DecidableEq U] [DecidableEq V]

def edges (adj : U → V → Prop) [DecidableRel adj] (l : Finset U) (r : Finset V) : ℕ :=
  ∑ y ∈ r, (l.filter (fun x => adj x y)).card

omit [DecidableEq U] [DecidableEq V] in
theorem edges_swap (adj : U → V → Prop) [DecidableRel adj] (l : Finset U) (r : Finset V) :
    edges adj l r = edges (fun y x => adj x y) r l := by
  simp only [edges, Finset.card_filter]
  exact Finset.sum_comm

theorem peel (adj : U → V → Prop) [DecidableRel adj] (l : Finset U) (r : Finset V) :
    ∃ l' ⊆ l, ∃ r' ⊆ r,
      (∀ x ∈ l', 3 ≤ (r'.filter (adj x)).card) ∧
      (∀ y ∈ r', 3 ≤ (l'.filter (fun x => adj x y)).card) ∧
      edges adj l r + 2*(l'.card+r'.card) ≤ edges adj l' r' + 2*(l.card+r.card) := by
  classical
  by_cases allL : ∀ x ∈ l, 3 ≤ (r.filter (adj x)).card
  · by_cases allR : ∀ y ∈ r, 3 ≤ (l.filter (fun x => adj x y)).card
    · exact ⟨l, Finset.Subset.rfl, r, Finset.Subset.rfl, allL, allR, by omega⟩
    · obtain ⟨y,hy,small⟩ : ∃ y ∈ r, (l.filter (fun x => adj x y)).card < 3 := by
        simpa only [not_forall, exists_prop, not_le] using allR
      obtain ⟨l',hl,r',hr,dl,dr,count⟩ := peel adj l (r.erase y)
      have dec := Finset.card_erase_add_one hy
      have changeCount : edges adj l (r.erase y) + (l.filter (fun x => adj x y)).card = edges adj l r :=
        Finset.sum_erase_add _ _ hy
      exact ⟨l',hl,r',hr.trans (Finset.erase_subset _ _),dl,dr,by omega⟩
  · obtain ⟨x,hx,small⟩ : ∃ x ∈ l, (r.filter (adj x)).card < 3 := by
      simpa only [not_forall, exists_prop, not_le] using allL
    obtain ⟨l',hl,r',hr,dl,dr,count⟩ := peel adj (l.erase x) r
    have dec := Finset.card_erase_add_one hx
    have changeCount : edges adj (l.erase x) r + (r.filter (adj x)).card = edges adj l r := by
      rw [edges_swap adj (l.erase x) r, edges_swap adj l r]
      exact Finset.sum_erase_add _ _ hx
    exact ⟨l',hl.trans (Finset.erase_subset _ _),r',hr,dl,dr,by omega⟩
termination_by l.card + r.card
decreasing_by all_goals have := Finset.card_erase_add_one ‹_ ∈ _›; omega

end CorePeeling

namespace ChainCover

variable {U R I : Type*} [Fintype U] [DecidableEq U] [Fintype R] [DecidableEq R] [Fintype I]

/-- A restricted system with at least three neighbors at each retained point needs
at least one prefix factor per unordered pair of retained points. -/
theorem induced_order_budget (rank : I → U → ℕ) (columns : R → Finset U)
    (codegree : ∀ x y, x ≠ y → ((star columns x) ∩ (star columns y)).card ≤ 1)
    (correct : ∀ a b, hits a (extent columns b) ↔
      ∀ i, hits a (extent (fun y => downClosure (rank i) (columns y)) b))
    (l : Finset U) (r : Finset R)
    (degree : ∀ x ∈ l, 3 ≤ (r.filter (fun y => x ∈ columns y)).card) :
    l.card.choose 2 ≤ Fintype.card I := by
  classical
  let small := restrictColumns l r columns
  have project (p : l) (t : r) (ht : t ∈ star small p) : t.val ∈ star columns p.val := by
    have hp : p.val ∈ columns t.val := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).2).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
  have deg (x : l) : 3 ≤ (star small x).card := by
    have eq : (star small x).image Subtype.val = r.filter (fun y => x.val ∈ columns y) := by
      ext y
      simp only [small, star, restrictColumns, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨z, h, rfl⟩
        exact ⟨z.prop, h⟩
      · rintro ⟨hy, h⟩
        exact ⟨⟨y, hy⟩, h, rfl⟩
    have h := degree x.val x.prop
    rwa [← eq, Finset.card_image_of_injective _ Subtype.val_injective] at h
  have co (x z : l) (ne : x ≠ z) : ((star small x) ∩ (star small z)).card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro a b ha hb
    apply Subtype.ext
    exact Finset.card_le_one_iff.mp
      (codegree x.val z.val (fun eq => ne (Subtype.ext eq))) (Finset.mem_inter.mpr
      ⟨project x a (Finset.mem_inter.mp ha).1, project z a (Finset.mem_inter.mp ha).2⟩)
      (Finset.mem_inter.mpr
      ⟨project x b (Finset.mem_inter.mp hb).1, project z b (Finset.mem_inter.mp hb).2⟩)
  have bound := binomial_lower_bound (fun i (x : l) => rank i x.val) small 3 2
    (by decide) deg co (restrict_exact rank columns correct l r)
  simpa using bound

end ChainCover

namespace ChainCost

open ChainCover

variable {U R I : Type*} [Fintype U] [DecidableEq U] [Fintype R] [DecidableEq R] [Fintype I]

theorem core_factors (columns : R → Finset U) (rank : I → U → ℕ)
    (codegree : ∀ x y, x ≠ y → ((star columns x) ∩ (star columns y)).card ≤ 1)
    (correct : ∀ a b, hits a (extent columns b) ↔
      ∀ i, hits a (extent (fun y => downClosure (rank i) (columns y)) b))
    (l : Finset U) (r : Finset R) :
    ∃ a ⊆ l, ∃ b ⊆ r,
      CorePeeling.edges (fun x y => x ∈ columns y) l r + 2*(a.card+b.card) ≤
        CorePeeling.edges (fun x y => x ∈ columns y) a b + 2*(l.card+r.card) ∧
      CorePeeling.edges (fun x y => x ∈ columns y) a b ≤ Fintype.card I := by
  obtain ⟨a,ha,b,hb,da,db,peel⟩ := CorePeeling.peel (fun x y => x ∈ columns y) l r
  have pairs := PairBudget.restricted_column_sum_le columns a b codegree db
  have orders := induced_order_budget rank columns codegree correct a b da
  exact ⟨a,ha,b,hb,peel,pairs.trans orders⟩

/-- Edge bound for prefix factors. The two resource hypotheses state the input-support
bound and the cost of making distinct factor functions available on actual wires. -/
theorem budget (columns : R → Finset U) (rank : I → U → ℕ)
    (codegree : ∀ x y, x ≠ y → ((star columns x) ∩ (star columns y)).card ≤ 1)
    (correct : ∀ a b, hits a (extent columns b) ↔
      ∀ i, hits a (extent (fun y => downClosure (rank i) (columns y)) b))
    (l : Finset U) (r : Finset R) (s : ℕ) (support : l.card+r.card ≤ s+1)
    (factors : l.card+r.card+Fintype.card I ≤ s+2) :
    CorePeeling.edges (fun x y => x ∈ columns y) l r ≤ 2*(s+1) := by
  obtain ⟨a,_,b,_,peel,core⟩ := core_factors columns rank codegree correct l r
  by_cases empty : a = ∅
  · subst a
    simp [CorePeeling.edges] at peel
    change (∑ y ∈ r, (l.filter (fun x => x ∈ columns y)).card) ≤ 2*(s+1)
    omega
  · have positive := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
    omega

/-- Exact conjunctions of nested-neighborhood supergraphs, with the explicit wire budgets. -/
theorem nested_budget (columns : R → Finset U) (large : I → R → Finset U)
    (codegree : ∀ x y, x ≠ y → ((star columns x) ∩ (star columns y)).card ≤ 1)
    (extensive : ∀ i r, columns r ⊆ large i r)
    (nested : ∀ i r t, large i r ⊆ large i t ∨ large i t ⊆ large i r)
    (correct : ∀ a b, hits a (extent columns b) ↔ ∀ i, hits a (extent (large i) b))
    (l : Finset U) (r : Finset R) (s : ℕ) (support : l.card+r.card ≤ s+1)
    (factors : l.card+r.card+Fintype.card I ≤ s+2) :
    CorePeeling.edges (fun x y => x ∈ columns y) l r ≤ 2*(s+1) := by
  obtain ⟨rank,exactness⟩ := nested_to_prefix columns large extensive nested correct
  exact budget columns rank codegree exactness l r s support factors

end ChainCost

namespace FactorWireCost

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity GraphCircuitSupport

/-- Count gates at and after the earliest selected gate. Indices start at zero. -/
theorem cost_of_prefix_counts {v s : ℕ} (J : Finset ℕ) (nonempty : J.Nonempty)
    (inside : J ⊆ Finset.range s) (support : ∀ j ∈ J, v ≤ (j+1)+1) :
    v + J.card ≤ s + 2 := by
  let first := J.min' nonempty
  have member : first ∈ J := J.min'_mem nonempty
  have last : first < s := Finset.mem_range.mp (inside member)
  have rest : J ⊆ Finset.Ico first s := by
    intro j hj
    exact Finset.mem_Ico.mpr ⟨J.min'_le _ hj, Finset.mem_range.mp (inside hj)⟩
  have count := Finset.card_le_card rest
  rw [Nat.card_Ico] at count
  have enough := support first member
  omega

/-- Gate j and its predecessors, with the wire emitted by j as output. -/
def gatePrefix (n : ℕ) (C : Circuit) (j : ℕ) : Circuit :=
  ⟨C.gates.take (j+1), n+j⟩

def gateFunction (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD (n+j) false

private theorem fold_length (gates : List Gate) (w : List Bool) :
    (gates.foldl gateStep w).length = w.length + gates.length := by
  induction gates generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, gateStep, Nat.add_comm, Nat.add_left_comm]

private theorem fold_extends (gates : List Gate) (w : List Bool) :
    ∃ extra, gates.foldl gateStep w = w ++ extra := by
  induction gates generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨extra, eq⟩ := ih (gateStep w g)
    exact ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: extra,
      by simpa [gateStep] using eq⟩

/-- Every following gate appends a wire, preserving the actual value of gate j. -/
theorem gatePrefix_function (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.size) :
    circuitFun n (gatePrefix n C j) = gateFunction n C j := by
  funext x
  let w := (C.gates.take (j+1)).foldl gateStep (List.ofFn x)
  have used : j+1 ≤ C.gates.length := hj
  have before : n+j < w.length := by
    simp only [w, fold_length, List.length_ofFn, List.length_take, Nat.min_eq_left used]
    omega
  obtain ⟨extra, eq⟩ := fold_extends (C.gates.drop (j+1)) w
  have full : C.wires (List.ofFn x) = w ++ extra := by
    change C.gates.foldl gateStep (List.ofFn x) = _
    calc
      _ = ((C.gates.take (j+1)) ++ C.gates.drop (j+1)).foldl gateStep (List.ofFn x) := by
        rw [List.take_append_drop]
      _ = _ := by simpa only [List.foldl_append, w] using eq
  change w.getD (n+j) false = (C.wires (List.ofFn x)).getD (n+j) false
  rw [full]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left before]

/-- If each selected gate computes an edge function with at least v nonisolated
vertices, the size pays for the active inputs and the number of selected gates. -/
theorem cost_of_graph_outputs {v n : ℕ} (C : Circuit) (J : Finset ℕ)
    (graphs : ℕ → SimpleGraph (Fin n)) [∀ j, DecidableRel (graphs j).Adj]
    (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (nonempty : J.Nonempty)
    (inside : J ⊆ Finset.range C.size)
    (active_count : ∀ j ∈ J, v ≤ (active (graphs j)).card)
    (computes : ∀ j ∈ J, gateFunction n C j = edge (graphs j)) :
    v + J.card ≤ C.size + 2 := by
  apply cost_of_prefix_counts J nonempty inside
  intro j hj
  have valid := Finset.mem_range.mp (inside hj)
  have eval := (gatePrefix_function n C j valid).trans (computes j hj)
  have limit := active_bound (graphs j) (gatePrefix n C j)
    (fun g hg => fan g (List.mem_of_mem_take hg)) eval
  have count : (gatePrefix n C j).size = j+1 := by
    exact (List.length_take ..).trans (Nat.min_eq_left (by exact valid))
  rw [count] at limit
  exact (active_count j hj).trans limit

end FactorWireCost

namespace ChainCost

open PEqualNP.CircuitLowerBounds GraphCircuitSupport FactorWireCost ChainCover

/-- J indexes gates, one for each retained factor. A factor with every original edge
depends on all original nonisolated vertices, giving the active-count premise below. -/
theorem materialized_bound {U R : Type*} [Fintype U] [DecidableEq U]
    [Fintype R] [DecidableEq R] {n : ℕ}
    (columns : R → Finset U) (l : Finset U) (r : Finset R) (C : Circuit)
    (J : Finset ℕ) (large : J → R → Finset U)
    (codegree : ∀ x y, x ≠ y → ((star columns x) ∩ (star columns y)).card ≤ 1)
    (extensive : ∀ i y, columns y ⊆ large i y)
    (nested : ∀ i y z, large i y ⊆ large i z ∨ large i z ⊆ large i y)
    (correct : ∀ a b, hits a (extent columns b) ↔ ∀ i, hits a (extent (large i) b))
    (graphs : ℕ → SimpleGraph (Fin n)) [∀ j, DecidableRel (graphs j).Adj]
    (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (some_gate : J.Nonempty) (inside : J ⊆ Finset.range C.size)
    (active_count : ∀ j ∈ J, l.card+r.card ≤ (active (graphs j)).card)
    (realized : ∀ j ∈ J, gateFunction n C j = edge (graphs j)) :
    CorePeeling.edges (fun x y => x ∈ columns y) l r ≤ 2*(C.size+1) := by
  have cost := cost_of_graph_outputs C J graphs fan some_gate inside active_count realized
  have positive := Finset.card_pos.mpr some_gate
  apply nested_budget columns large codegree extensive nested correct l r C.size
  · omega
  · simpa using cost

end ChainCost
