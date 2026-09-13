import ZFVP.ModelTheory.SchmerlFiniteSpecialization
import ZFVP.ModelTheory.SchmerlBranchMarkers

/-! The ordinary finite strict-specialization forcing used on the Aronszajn
core of Baumgartner's reduction. This differs from the finite weak-coloring
attempts, whose chain-condition obstruction is proved separately.
-/

namespace ZFVP.Schmerl

open Set

universe u

variable (T : Type u) [PartialOrder T]

/-- A finite partial coloring in which equal-colored comparable nodes coincide. -/
def StrictCondition := {p : SpecializationCondition ((· ≤ ·) : T → T → Prop) //
  ∀ x y n, (x, n) ∈ p.graph → (y, n) ∈ p.graph → x ≤ y → x = y}

namespace StrictCondition

variable {T}

instance : PartialOrder (StrictCondition T) := inferInstanceAs (PartialOrder (Subtype _))

abbrev graph (p : StrictCondition T) : Set (T × ℕ) := p.val.graph

theorem finite (p : StrictCondition T) : p.graph.Finite := p.val.finite

theorem functional (p : StrictCondition T) {x : T} {m n : ℕ}
    (hm : (x, m) ∈ p.graph) (hn : (x, n) ∈ p.graph) : m = n :=
  p.val.functional x m n hm hn

theorem strict (p : StrictCondition T) {x y : T} {n : ℕ}
    (hx : (x, n) ∈ p.graph) (hy : (y, n) ∈ p.graph) (hxy : x ≤ y) : x = y :=
  p.property x y n hx hy hxy

@[ext] theorem ext {p q : StrictCondition T} (h : p.graph = q.graph) : p = q :=
  Subtype.ext (SpecializationCondition.ext h)

@[simp] theorem le_iff {p q : StrictCondition T} : p ≤ q ↔ q.graph ⊆ p.graph := Iff.rfl

def empty : StrictCondition T := ⟨SpecializationCondition.empty, by
  intro x y n hx
  exact hx.elim⟩

instance : OrderTop (StrictCondition T) where
  top := empty
  le_top _ := Set.empty_subset _

/-- Build a condition directly from a finite functional strict-coloring graph. -/
def ofGraph (g : Set (T × ℕ)) (hfin : g.Finite)
    (hfun : ∀ x m n, (x, m) ∈ g → (x, n) ∈ g → m = n)
    (hstrict : ∀ x y n, (x, n) ∈ g → (y, n) ∈ g → x ≤ y → x = y) :
    StrictCondition T :=
  ⟨{ graph := g, finite := hfin, functional := hfun,
     specializes := by
       intro x y z n hx hy hz hxy hxz
       exact Or.inl (by simpa only [← hstrict x y n hx hy hxy] using hxz) }, hstrict⟩

/-- Every subgraph of a condition remains a condition. -/
def restrict (p : StrictCondition T) (g : Set (T × ℕ)) (hg : g ⊆ p.graph) :
    StrictCondition T :=
  ofGraph g (p.finite.subset hg)
    (fun _ _ _ hm hn ↦ p.functional (hg hm) (hg hn))
    (fun _ _ _ hx hy hxy ↦ p.strict (hg hx) (hg hy) hxy)

@[simp] theorem graph_restrict (p : StrictCondition T) (g : Set (T × ℕ))
    (hg : g ⊆ p.graph) : (p.restrict g hg).graph = g := rfl

/-- Delete an assignment; this is the induction operation in the ccc proof. -/
def erase (p : StrictCondition T) (a : T × ℕ) : StrictCondition T :=
  p.restrict (p.graph \ {a}) Set.sdiff_subset

@[simp] theorem graph_erase (p : StrictCondition T) (a : T × ℕ) :
    (p.erase a).graph = p.graph \ {a} := rfl

/-- Compatibility is equivalent to consistent assignments and no cross-condition
collision between comparable nodes of the same color. -/
def Compatible (p q : StrictCondition T) : Prop := ∃ s, s ≤ p ∧ s ≤ q

theorem compatible_iff {p q : StrictCondition T} : Compatible p q ↔
    (∀ x m n, (x, m) ∈ p.graph → (x, n) ∈ q.graph → m = n) ∧
    (∀ x y n, (x, n) ∈ p.graph → (y, n) ∈ q.graph → x ≤ y ∨ y ≤ x → x = y) := by
  constructor
  · rintro ⟨s, hsp, hsq⟩
    refine ⟨fun _ _ _ hm hn ↦ s.functional (hsp hm) (hsq hn), ?_⟩
    intro x y n hx hy hxy
    rcases hxy with hxy | hyx
    · exact s.strict (hsp hx) (hsq hy) hxy
    · exact (s.strict (hsq hy) (hsp hx) hyx).symm
  · rintro ⟨hfun, hstrict⟩
    refine ⟨ofGraph (p.graph ∪ q.graph) (p.finite.union q.finite) ?_ ?_,
      Set.subset_union_left, Set.subset_union_right⟩
    · intro x m n hm hn
      rcases hm with hm | hm <;> rcases hn with hn | hn
      · exact p.functional hm hn
      · exact hfun x m n hm hn
      · exact (hfun x n m hn hm).symm
      · exact q.functional hm hn
    · intro x y n hx hy hxy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact p.strict hx hy hxy
      · exact hstrict x y n hx hy (Or.inl hxy)
      · exact (hstrict y x n hy hx (Or.inr hxy)).symm
      · exact q.strict hx hy hxy

/-- Incompatibility requires a pair of comparable nodes across the two graphs. -/
theorem exists_comparable_of_not_compatible {p q : StrictCondition T}
    (h : ¬ Compatible p q) :
    ∃ a ∈ p.graph, ∃ b ∈ q.graph, a.1 ≤ b.1 ∨ b.1 ≤ a.1 := by
  by_contra hn
  push Not at hn
  apply h
  apply compatible_iff.mpr
  constructor
  · intro x m n hm hn'
    exact ((hn (x, m) hm (x, n) hn').1 le_rfl).elim
  · intro x y n hx hy hxy
    exact (not_or_intro (hn (x, n) hx (y, n) hy).1
      (hn (x, n) hx (y, n) hy).2 hxy).elim

/-- Removing an assignment shared by both conditions preserves incompatibility. -/
theorem compatible_of_erase {p q : StrictCondition T} {a : T × ℕ}
    (hp : a ∈ p.graph) (hq : a ∈ q.graph)
    (h : Compatible (p.erase a) (q.erase a)) : Compatible p q := by
  obtain ⟨hfun, hstrict⟩ := compatible_iff.mp h
  apply compatible_iff.mpr
  constructor
  · intro x m n hm hn
    by_cases hem : (x, m) = a
    · exact q.functional (hem.symm ▸ hq) hn
    by_cases hen : (x, n) = a
    · exact p.functional hm (hen.symm ▸ hp)
    exact hfun x m n ⟨hm, hem⟩ ⟨hn, hen⟩
  · intro x y n hx hy hxy
    by_cases hex : (x, n) = a
    · rcases hxy with hxy | hyx
      · exact q.strict (hex.symm ▸ hq) hy hxy
      · exact (q.strict hy (hex.symm ▸ hq) hyx).symm
    by_cases hey : (y, n) = a
    · rcases hxy with hxy | hyx
      · exact p.strict hx (hey.symm ▸ hp) hxy
      · exact (p.strict (hey.symm ▸ hp) hx hyx).symm
    exact hstrict x y n ⟨hx, hex⟩ ⟨hy, hey⟩ hxy

theorem erase_injOn (a : T × ℕ) : Set.InjOn (fun p : StrictCondition T ↦ p.erase a)
    {p | a ∈ p.graph} := by
  intro p hp q hq heq
  apply ext
  have heq' := congrArg graph heq
  apply Set.ext
  intro b
  by_cases hb : b = a
  · subst b; exact iff_of_true hp hq
  · have : b ∈ (p.erase a).graph ↔ b ∈ (q.erase a).graph := Set.ext_iff.mp heq' b
    simpa only [graph_erase, Set.mem_sdiff, Set.mem_singleton_iff, hb, not_false_eq_true,
      and_true] using this

/-- A fresh unused color can be assigned to any undecided node. -/
def insert (p : StrictCondition T) (a : T) (n : ℕ)
    (ha : ∀ m, (a, m) ∉ p.graph) (hn : ∀ x, (x, n) ∉ p.graph) :
    StrictCondition T :=
  ⟨p.val.insert a n ha hn, by
    intro x y k hx hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact (Prod.mk.inj hx).1.trans (Prod.mk.inj hy).1.symm
    · exact (hn y ((Prod.mk.inj hx).2 ▸ hy)).elim
    · exact (hn x ((Prod.mk.inj hy).2 ▸ hx)).elim
    · exact p.strict hx hy hxy⟩

def decides (x : T) : Set (StrictCondition T) := {p | ∃ n, (x, n) ∈ p.graph}

theorem decides_dense (x : T) (p : StrictCondition T) : ∃ q ≤ p, q ∈ decides x := by
  classical
  by_cases hx : ∃ n, (x, n) ∈ p.graph
  · exact ⟨p, le_rfl, hx⟩
  · have hnew : ∀ n, (x, n) ∉ p.graph := by simpa using hx
    obtain ⟨n, hn⟩ := p.val.exists_unused_color
    exact ⟨p.insert x n hnew hn, Set.subset_insert _ _, n, Set.mem_insert _ _⟩

/-- A directed family meeting the deciding dense sets yields a strict coloring. -/
theorem exists_coloring {G : Set (StrictCondition T)} (hG : DirectedOn (· ≥ ·) G)
    (hmeets : ∀ x, ∃ p ∈ G, p ∈ decides x) :
    ∃ f : T → ℕ, BranchMarkers.StrictSpecializes f ∧
      ∀ p ∈ G, ∀ x n, (x, n) ∈ p.graph → f x = n := by
  classical
  have ht : ∀ x, ∃ n, ∃ p ∈ G, (x, n) ∈ p.graph := by
    intro x
    obtain ⟨p, hp, n, hn⟩ := hmeets x
    exact ⟨n, p, hp, hn⟩
  choose f pf hpf hf using ht
  have hcolor (p : StrictCondition T) (hp : p ∈ G) (x : T) (n : ℕ)
      (hn : (x, n) ∈ p.graph) : f x = n := by
    obtain ⟨q, _, hqp, hqf⟩ := hG p hp (pf x) (hpf x)
    exact q.functional (hqf (hf x)) (hqp hn)
  refine ⟨f, ?_, hcolor⟩
  intro x y hxy heq
  obtain ⟨p, _, hpx, hpy⟩ := hG (pf x) (hpf x) (pf y) (hpf y)
  exact hxy.ne (p.strict (hpx (hf x)) (hpy (heq.symm ▸ hf y)) hxy.le)

end StrictCondition

end ZFVP.Schmerl
