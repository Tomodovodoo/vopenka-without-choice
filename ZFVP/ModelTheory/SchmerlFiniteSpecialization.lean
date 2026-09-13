import ZFVP.ModelTheory.SchmerlWeakSpecialization

/-! Finite conditions for the weak specialization used in Schmerl's argument.
Every node has a dense set of conditions assigning it a color. A directed family
meeting these dense sets has a total weakly specializing union. The chain
condition and the construction of an omega-one-preserving generic extension are
separate obligations and are not asserted here.
-/

namespace ZFVP.Schmerl

open Set

universe u

variable {T : Type u}

/-- A finite partial coloring obeying the monochromatic-fork condition. -/
structure SpecializationCondition (r : T → T → Prop) where
  graph : Set (T × ℕ)
  finite : graph.Finite
  functional : ∀ x m n, (x, m) ∈ graph → (x, n) ∈ graph → m = n
  specializes : ∀ x y z n, (x, n) ∈ graph → (y, n) ∈ graph → (z, n) ∈ graph →
    r x y → r x z → r y z ∨ r z y

namespace SpecializationCondition

variable {r : T → T → Prop}

@[ext] theorem ext {p q : SpecializationCondition r} (h : p.graph = q.graph) : p = q := by
  cases p
  cases q
  cases h
  rfl

/-- Stronger conditions extend the finite graph. -/
instance : PartialOrder (SpecializationCondition r) where
  le p q := q.graph ⊆ p.graph
  le_refl _ := Set.Subset.rfl
  le_trans _ _ _ hpq hqr := hqr.trans hpq
  le_antisymm _ _ hpq hqp := ext (Set.Subset.antisymm hqp hpq)

@[simp] theorem le_iff {p q : SpecializationCondition r} : p ≤ q ↔ q.graph ⊆ p.graph :=
  Iff.rfl

/-- The empty condition. -/
def empty : SpecializationCondition r where
  graph := ∅
  finite := Set.finite_empty
  functional := by simp
  specializes := by simp

instance : OrderTop (SpecializationCondition r) where
  top := empty
  le_top _ := Set.empty_subset _

/-- A finite condition leaves some natural-number color unused. -/
theorem exists_unused_color (p : SpecializationCondition r) :
    ∃ n, ∀ x, (x, n) ∉ p.graph := by
  obtain ⟨n, hn⟩ := (p.finite.image Prod.snd).exists_notMem
  exact ⟨n, fun x hx ↦ hn ⟨(x, n), hx, rfl⟩⟩

/-- Assign a previously uncolored node a color unused in the condition. -/
def insert (p : SpecializationCondition r) (a : T) (n : ℕ)
    (ha : ∀ m, (a, m) ∉ p.graph) (hn : ∀ x, (x, n) ∉ p.graph) :
    SpecializationCondition r where
  graph := Set.insert (a, n) p.graph
  finite := p.finite.insert _
  functional := by
    intro x m k hm hk
    rcases hm with hm | hm <;> rcases hk with hk | hk
    · exact (Prod.mk.inj hm).2.trans (Prod.mk.inj hk).2.symm
    · have hx : x = a := (Prod.mk.inj hm).1
      exact (ha k (hx ▸ hk)).elim
    · have hx : x = a := (Prod.mk.inj hk).1
      exact (ha m (hx ▸ hm)).elim
    · exact p.functional x m k hm hk
  specializes := by
    intro x y z k hx hy hz hxy hxz
    have hfresh : ∀ t, (t, n) ∈ Set.insert (a, n) p.graph → t = a := by
      intro t ht
      rcases ht with ht | ht
      · exact (Prod.mk.inj ht).1
      · exact (hn t ht).elim
    by_cases hkn : k = n
    · subst k
      have hxa := hfresh x hx
      have hya := hfresh y hy
      have hza := hfresh z hz
      exact Or.inl (by simpa only [hxa, hya, hza] using hxy)
    · have old : ∀ t, (t, k) ∈ Set.insert (a, n) p.graph → (t, k) ∈ p.graph := by
        intro t ht
        rcases ht with ht | ht
        · exact (hkn (Prod.mk.inj ht).2).elim
        · exact ht
      exact p.specializes x y z k (old x hx) (old y hy) (old z hz) hxy hxz

theorem insert_le (p : SpecializationCondition r) (a : T) (n : ℕ)
    (ha : ∀ m, (a, m) ∉ p.graph) (hn : ∀ x, (x, n) ∉ p.graph) :
    p.insert a n ha hn ≤ p := Set.subset_insert _ _

@[simp] theorem mem_insert_self (p : SpecializationCondition r) (a : T) (n : ℕ)
    (ha : ∀ m, (a, m) ∉ p.graph) (hn : ∀ x, (x, n) ∉ p.graph) :
    (a, n) ∈ (p.insert a n ha hn).graph := Set.mem_insert _ _

/-- The dense set demanding a color at the node `x`. -/
def decides (x : T) : Set (SpecializationCondition r) :=
  {p | ∃ n, (x, n) ∈ p.graph}

/-- Every condition extends to one deciding any specified node. -/
theorem decides_dense (x : T) (p : SpecializationCondition r) :
    ∃ q ≤ p, q ∈ decides x := by
  classical
  by_cases hx : ∃ n, (x, n) ∈ p.graph
  · exact ⟨p, le_rfl, hx⟩
  · have hnew : ∀ n, (x, n) ∉ p.graph := by simpa using hx
    obtain ⟨n, hn⟩ := p.exists_unused_color
    exact ⟨p.insert x n hnew hn, p.insert_le x n hnew hn, n,
      p.mem_insert_self x n hnew hn⟩

/-- Membership in the union of a family of condition graphs. -/
def UnionColor (G : Set (SpecializationCondition r)) (x : T) (n : ℕ) : Prop :=
  ∃ p ∈ G, (x, n) ∈ p.graph

/-- Directedness prevents conflicting color assignments in the union. -/
theorem union_functional {G : Set (SpecializationCondition r)}
    (hG : DirectedOn (· ≥ ·) G) {x : T} {m n : ℕ}
    (hm : UnionColor G x m) (hn : UnionColor G x n) : m = n := by
  obtain ⟨p, hp, hpm⟩ := hm
  obtain ⟨q, hq, hqn⟩ := hn
  obtain ⟨s, _, hsp, hsq⟩ := hG p hp q hq
  exact s.functional x m n (hsp hpm) (hsq hqn)

/-- A common strengthening transfers the finite fork condition to the union. -/
theorem union_specializes {G : Set (SpecializationCondition r)}
    (hG : DirectedOn (· ≥ ·) G) {x y z : T} {n : ℕ}
    (hx : UnionColor G x n) (hy : UnionColor G y n) (hz : UnionColor G z n)
    (hxy : r x y) (hxz : r x z) : r y z ∨ r z y := by
  obtain ⟨p, hp, hpx⟩ := hx
  obtain ⟨q, hq, hqy⟩ := hy
  obtain ⟨s, hs, hsz⟩ := hz
  obtain ⟨t, ht, htp, htq⟩ := hG p hp q hq
  obtain ⟨v, _, hvt, hvs⟩ := hG t ht s hs
  exact v.specializes x y z n (hvt (htp hpx)) (hvt (htq hqy)) (hvs hsz) hxy hxz

/-- Meeting every deciding set makes the union total. -/
theorem union_total {G : Set (SpecializationCondition r)}
    (hmeets : ∀ x, ∃ p ∈ G, p ∈ decides x) (x : T) : ∃ n, UnionColor G x n := by
  obtain ⟨p, hp, n, hn⟩ := hmeets x
  exact ⟨n, p, hp, hn⟩

/-- The coloring read from a total directed union. -/
noncomputable def coloring (G : Set (SpecializationCondition r))
    (hmeets : ∀ x, ∃ p ∈ G, p ∈ decides x) (x : T) : ℕ :=
  Classical.choose (union_total hmeets x)

theorem coloring_mem (G : Set (SpecializationCondition r))
    (hmeets : ∀ x, ∃ p ∈ G, p ∈ decides x) (x : T) :
    UnionColor G x (coloring G hmeets x) := Classical.choose_spec (union_total hmeets x)

/-- A total directed union is a weakly specializing function, with every
condition's assignments preserved exactly. -/
theorem coloring_spec {G : Set (SpecializationCondition r)}
    (hG : DirectedOn (· ≥ ·) G) (hmeets : ∀ x, ∃ p ∈ G, p ∈ decides x) :
    WeaklySpecializes r (coloring G hmeets) ∧
      ∀ x n, UnionColor G x n ↔ coloring G hmeets x = n := by
  have hiff : ∀ x n, UnionColor G x n ↔ coloring G hmeets x = n := by
    intro x n
    constructor
    · exact fun hn ↦ union_functional hG (coloring_mem G hmeets x) hn
    · intro heq
      exact heq ▸ coloring_mem G hmeets x
  refine ⟨?_, hiff⟩
  intro x y z hxy hxz hfy hfz
  exact union_specializes hG (coloring_mem G hmeets x)
    ((hiff y _).mpr hfy.symm) ((hiff z _).mpr hfz.symm) hxy hxz

/-- Compatibility means having a common stronger condition. -/
def Compatible (p q : SpecializationCondition r) : Prop := ∃ s, s ≤ p ∧ s ≤ q

theorem compatible_self (p : SpecializationCondition r) : Compatible p p :=
  ⟨p, le_rfl, le_rfl⟩

/-- Two conditions are incompatible if their union would contain a
monochromatic fork with incomparable tips. -/
theorem not_compatible_of_fork {p q : SpecializationCondition r} {a x y : T} {n : ℕ}
    (ha : (a, n) ∈ p.graph) (hx : (x, n) ∈ p.graph) (hy : (y, n) ∈ q.graph)
    (hax : r a x) (hay : r a y) (hxy : ¬ (r x y ∨ r y x)) : ¬ Compatible p q := by
  rintro ⟨s, hsp, hsq⟩
  exact hxy (s.specializes a x y n (hsp ha) (hsp hx) (hsq hy) hax hay)

/-- The countable chain condition for this forcing order. -/
def HasCountableAntichains (r : T → T → Prop) : Prop :=
  ∀ A : Set (SpecializationCondition r),
    A.Pairwise (fun p q ↦ ¬ Compatible p q) → A.Countable

section Tree

variable [PartialOrder T]

/-- A constant coloring on a finite chain is a valid condition. -/
def monochromatic (A : Set T) (hfin : A.Finite) (hchain : IsChain (· ≤ ·) A)
    (n : ℕ) : SpecializationCondition (fun x y : T ↦ x ≤ y) where
  graph := A ×ˢ {n}
  finite := hfin.prod (Set.finite_singleton n)
  functional := by
    intro x m k hm hk
    exact hm.2.trans hk.2.symm
  specializes := by
    intro x y z k _ hy hz _ _
    exact hchain.total hy.1 hz.1

/-- The condition assigning the same color to a root and a node above it. -/
def rootCondition (a x : T) (hax : a ≤ x) :
    SpecializationCondition (fun x y : T ↦ x ≤ y) :=
  monochromatic {a, x} (Set.toFinite _) (IsChain.pair hax) 0

theorem root_mem_rootCondition (a x : T) (hax : a ≤ x) :
    (a, 0) ∈ (rootCondition a x hax).graph := ⟨Or.inl rfl, rfl⟩

theorem node_mem_rootCondition (a x : T) (hax : a ≤ x) :
    (x, 0) ∈ (rootCondition a x hax).graph := ⟨Or.inr rfl, rfl⟩

/-- An antichain above a common root gives pairwise incompatible finite attempts. -/
theorem rootConditions_incompatible {a x y : T} (hax : a ≤ x) (hay : a ≤ y)
    (hxy : ¬ (x ≤ y ∨ y ≤ x)) :
    ¬ Compatible (rootCondition a x hax) (rootCondition a y hay) :=
  not_compatible_of_fork (root_mem_rootCondition a x hax)
    (node_mem_rootCondition a x hax) (node_mem_rootCondition a y hay) hax hay hxy

/-- If all finite weak-specialization attempts have the ccc, every antichain
above a fixed node is countable. Thus uncountable such antichains obstruct the
literal finite-attempt forcing; an appropriate specializing forcing needs
additional restrictions or a different construction. -/
theorem countable_of_countableAntichains (hccc : HasCountableAntichains (T := T) (· ≤ ·))
    {a : T} {A : Set T} (hroot : ∀ x ∈ A, a ≤ x)
    (hanti : A.Pairwise (fun x y ↦ ¬ (x ≤ y ∨ y ≤ x))) : A.Countable := by
  classical
  let f : A → SpecializationCondition (fun x y : T ↦ x ≤ y) :=
    fun x ↦ rootCondition a x (hroot x x.property)
  have hinc : ∀ x y : A, x ≠ y → ¬ Compatible (f x) (f y) := by
    intro x y hxy
    exact rootConditions_incompatible (hroot x x.property) (hroot y y.property)
      (hanti x.property y.property (fun h ↦ hxy (Subtype.ext h)))
  have hfinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    exact hinc x y hne (hxy ▸ compatible_self (f x))
  have hcount : (Set.range f).Countable := by
    apply hccc
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    exact hinc x y (fun h ↦ hxy (congrArg f h))
  let : Countable (Set.range f) := hcount.to_subtype
  have hinj : Function.Injective
      (fun x ↦ (⟨f x, Set.mem_range_self x⟩ : Set.range f)) :=
    fun _ _ h ↦ hfinj (congrArg Subtype.val h)
  let : Countable A := hinj.countable
  exact Set.to_countable A

end Tree

end SpecializationCondition

end ZFVP.Schmerl
