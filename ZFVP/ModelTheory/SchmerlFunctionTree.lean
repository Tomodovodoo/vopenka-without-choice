import ZFVP.ModelTheory.SchmerlDefinableBranchBound
import ZFVP.ModelTheory.ConstantStructure
import ZFVP.SetTheory.FinitePartialFunctions
import ZFVP.SetTheory.FiniteSequences

/-! The finite-function trees used in the Schmerl construction. Domains run
through a cofinal chain of internally finite subsets. Branches correspond to
filters which cover every chosen domain; this coverage is stated explicitly.
-/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u v

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {I : Type v} [LinearOrder I]

/-- A strictly indexed, cofinal chain of internally finite subsets of `s`. -/
structure FiniteDomainChain (s : V) (I : Type v) [LinearOrder I] where
  domain : I → V
  finite : ∀ i, IsInternallyFinite (domain i)
  subset : ∀ i, domain i ⊆ s
  monotone : ∀ ⦃i j⦄, i ≤ j → domain i ⊆ domain j
  injective : Function.Injective domain
  cofinal : ∀ a, a ⊆ s → IsInternallyFinite a → ∃ i, a ⊆ domain i

variable {s : V} (C : FiniteDomainChain s I)

theorem FiniteDomainChain.domain_subset_iff (i j : I) : C.domain i ⊆ C.domain j ↔ i ≤ j := by
  constructor
  · intro hij
    by_contra hn
    exact hn (C.injective (SetTheory.subset_antisymm hij (C.monotone (le_of_not_ge hn)))).le
  · exact fun hij ↦ C.monotone hij

/-- A node is an internal binary function on one selected domain. -/
structure FunctionTreeNode where
  level : I
  graph : V
  function : graph ∈ ((2 : ℕ) : V) ^ C.domain level

namespace FunctionTreeNode

variable {C}

@[ext] theorem ext {a b : FunctionTreeNode C} (hl : a.level = b.level)
    (hg : a.graph = b.graph) : a = b := by
  cases a
  cases b
  cases hl
  cases hg
  rfl

instance (a : FunctionTreeNode C) : IsFunction a.graph := IsFunction.of_mem a.function

@[simp] theorem domain_graph (a : FunctionTreeNode C) :
    domain a.graph = C.domain a.level := domain_eq_of_mem_function a.function

theorem graph_injective : Function.Injective (FunctionTreeNode.graph (C := C)) := by
  intro a b hab
  have hd := congrArg domain hab
  rw [domain_graph, domain_graph] at hd
  exact ext (C.injective hd) hab

instance : LE (FunctionTreeNode C) where
  le a b := a.level ≤ b.level ∧ a.graph ⊆ b.graph

theorem le_def (a b : FunctionTreeNode C) :
    a ≤ b ↔ a.level ≤ b.level ∧ a.graph ⊆ b.graph := Iff.rfl

instance : PartialOrder (FunctionTreeNode C) where
  le_refl a := ⟨le_rfl, subset_refl _⟩
  le_trans _ _ _ hab hbc := ⟨hab.1.trans hbc.1, subset_trans hab.2 hbc.2⟩
  le_antisymm _ _ hab hba := ext (le_antisymm hab.1 hba.1)
    (SetTheory.subset_antisymm hab.2 hba.2)

theorem le_iff_graph_subset (a b : FunctionTreeNode C) : a ≤ b ↔ a.graph ⊆ b.graph := by
  constructor
  · exact fun h ↦ h.2
  · intro hab
    refine ⟨?_, hab⟩
    have hd : C.domain a.level ⊆ C.domain b.level := by
      rw [← domain_graph a, ← domain_graph b]
      intro x hx
      obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
      exact mem_domain_of_kpair_mem (hab _ hxy)
    by_contra hn
    have hba := C.monotone (le_of_not_ge hn)
    exact hn (C.injective (SetTheory.subset_antisymm hd hba)).le

theorem subset_of_compatible {f g : V} [IsFunction f] [IsFunction g]
    (hdom : domain f ⊆ domain g)
    (hcompat : ∀ x y z, ⟨x, y⟩ₖ ∈ f → ⟨x, z⟩ₖ ∈ g → y = z) : f ⊆ g := by
  intro p hp
  obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hp
  obtain ⟨z, hz⟩ := mem_domain_iff.mp (hdom x (mem_domain_of_kpair_mem hp))
  exact hcompat x y z hp hz ▸ hz

theorem le_of_common_above {a b d : FunctionTreeNode C}
    (had : a ≤ d) (hbd : b ≤ d) (hab : a.level ≤ b.level) : a ≤ b := by
  refine ⟨hab, subset_of_compatible ?_ ?_⟩
  · rw [domain_graph, domain_graph]
    exact C.monotone hab
  · intro x y z hxy hxz
    exact IsFunction.unique (had.2 _ hxy) (hbd.2 _ hxz)

theorem tree : IsTreeOrder (FunctionTreeNode C) := by
  intro a b d had hbd
  rcases le_total a.level b.level with hab | hba
  · exact Or.inl (le_of_common_above had hbd hab)
  · exact Or.inr (le_of_common_above hbd had hba)

theorem level_strictMono : StrictMono (FunctionTreeNode.level (C := C)) := by
  intro a b hab
  refine lt_of_le_of_ne hab.le.1 ?_
  intro hl
  apply hab.ne
  apply ext hl
  apply function_eq_of_subset a.function
  · simpa only [hl] using b.function
  · exact hab.le.2

/-- Restriction supplies the predecessor at every earlier rank. -/
noncomputable def atLevel (b : FunctionTreeNode C) (i : I) (hi : i ≤ b.level) :
    FunctionTreeNode C where
  level := i
  graph := b.graph ↾ (C.domain i)
  function := function_restrict_mem b.function (C.monotone hi)

theorem atLevel_le (b : FunctionTreeNode C) {i : I} (hi : i ≤ b.level) :
    b.atLevel i hi ≤ b := ⟨hi, restrict_subset _ _⟩

/-- The actual function tree, ranked by the index order of its domains. -/
noncomputable def rankedTree : RankedTree (FunctionTreeNode C) I where
  tree := tree
  rank := FunctionTreeNode.level
  strictMono := level_strictMono
  onto i := ⟨⟨i, constantGraph (C.domain i) ((0 : ℕ) : V),
    constantGraph_mem_function _ _ _ (by simp)⟩, rfl⟩
  predecessor b i hi := ⟨b.atLevel i hi.le,
    lt_of_le_of_ne (b.atLevel_le hi.le) (fun heq ↦ hi.ne (congrArg FunctionTreeNode.level heq)), rfl⟩

noncomputable def codeEmbedding : FunctionTreeNode C ↪ V := ⟨FunctionTreeNode.graph, graph_injective⟩

theorem graph_mem_finitePartialFunctions (a : FunctionTreeNode C) :
    a.graph ∈ finitePartialFunctions s ((2 : ℕ) : V) := by
  refine (mem_finitePartialFunctions _ _ _).mpr ⟨?_, inferInstance, ?_⟩
  · exact subset_trans (subset_prod_of_mem_function a.function)
      (prod_subset_prod_of_subset (C.subset a.level) (subset_refl _))
  · rw [domain_graph]
    exact C.finite a.level

theorem mem_graph_range_iff (p : V) : p ∈ Set.range (FunctionTreeNode.graph (C := C)) ↔
    p ∈ finitePartialFunctions s ((2 : ℕ) : V) ∧ domain p ∈ Set.range C.domain := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.graph_mem_finitePartialFunctions, a.level, a.domain_graph.symm⟩
  · rintro ⟨hp, i, hi⟩
    let : IsFunction p := ((mem_finitePartialFunctions _ _ _).mp hp).2.1
    have hf : p ∈ ((2 : ℕ) : V) ^ C.domain i := by
      rw [hi]
      exact mem_function_of_mem_function_of_subset (IsFunction.mem_function p)
        (finitePartialFunction_range hp)
    exact ⟨⟨i, p, hf⟩, rfl⟩

end FunctionTreeNode

/-- A directed, downward closed family of internal finite binary functions. -/
def IsFunctionFilter (F : V → Prop) : Prop :=
  (∀ p, F p → p ∈ finitePartialFunctions s ((2 : ℕ) : V)) ∧
  (∃ p, F p) ∧
  (∀ p q, F p → F q → ∃ r, F r ∧ p ⊆ r ∧ q ⊆ r) ∧
  ∀ p q, F p → q ⊆ p → F q

/-- The filter generated by a branch, including all internal finite subfunctions. -/
def filterOfBranch (B : Set (FunctionTreeNode C)) (p : V) : Prop :=
  p ∈ finitePartialFunctions s ((2 : ℕ) : V) ∧ ∃ a ∈ B, p ⊆ a.graph

theorem filterOfBranch_isFilter [Nonempty I] {B : Set (FunctionTreeNode C)}
    (hB : (FunctionTreeNode.rankedTree (C := C)).IsBranch B) :
    IsFunctionFilter (s := s) (filterOfBranch C B) := by
  refine ⟨fun _ hp ↦ hp.1, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, _⟩ := hB.2 (Classical.arbitrary I)
    exact ⟨a.graph, a.graph_mem_finitePartialFunctions, a, ha, subset_refl _⟩
  · rintro p q ⟨_, a, ha, hpa⟩ ⟨_, b, hb, hqb⟩
    rcases hB.1.total ha hb with hab | hba
    · exact ⟨b.graph, ⟨b.graph_mem_finitePartialFunctions, b, hb, subset_refl _⟩,
        subset_trans hpa hab.2, hqb⟩
    · exact ⟨a.graph, ⟨a.graph_mem_finitePartialFunctions, a, ha, subset_refl _⟩,
        hpa, subset_trans hqb hba.2⟩
  · rintro p q ⟨hp, a, ha, hpa⟩ hqp
    exact ⟨finitePartialFunction_subset hp hqp, a, ha, subset_trans hqp hpa⟩

theorem filterOfBranch_graph_iff {B : Set (FunctionTreeNode C)}
    (hB : (FunctionTreeNode.rankedTree (C := C)).IsBranch B) (a : FunctionTreeNode C) :
    filterOfBranch C B a.graph ↔ a ∈ B := by
  constructor
  · rintro ⟨_, b, hb, hab⟩
    have hi : a.level ≤ b.level := by
      by_contra hn
      have hba : C.domain b.level ⊆ C.domain a.level := C.monotone (le_of_not_ge hn)
      have heq : a.graph = b.graph := FunctionTreeNode.subset_of_compatible
        (f := b.graph) (g := a.graph) (by simpa only [FunctionTreeNode.domain_graph] using hba)
        (fun x y z hxy hxz ↦ IsFunction.unique hxy (hab _ hxz)) |>
          SetTheory.subset_antisymm hab
      exact hn (congrArg FunctionTreeNode.level (FunctionTreeNode.graph_injective heq)).le
    exact branch_downward_closed FunctionTreeNode.tree hB.isMaxChain hb ⟨hi, hab⟩
  · intro ha
    exact ⟨a.graph_mem_finitePartialFunctions, a, ha, subset_refl _⟩

theorem filterOfBranch_covers {B : Set (FunctionTreeNode C)}
    (hB : (FunctionTreeNode.rankedTree (C := C)).IsBranch B) (i : I) :
    ∃ p, filterOfBranch C B p ∧ C.domain i ⊆ domain p := by
  obtain ⟨a, ha, hlevel⟩ := hB.2 i
  change a.level = i at hlevel
  refine ⟨a.graph, (filterOfBranch_graph_iff C hB a).mpr ha, ?_⟩
  rw [FunctionTreeNode.domain_graph, hlevel]

/-- The tree branch recovered from a filter. Coverage is needed to make it cofinal. -/
def branchOfFilter (F : V → Prop) : Set (FunctionTreeNode C) := {a | F a.graph}

theorem branchOfFilter_isBranch {F : V → Prop} (hF : IsFunctionFilter (s := s) F)
    (hcover : ∀ i, ∃ p, F p ∧ C.domain i ⊆ domain p) :
    (FunctionTreeNode.rankedTree (C := C)).IsBranch (branchOfFilter C F) := by
  have hcompat : ∀ p q, F p → F q → ∀ x y z,
      ⟨x, y⟩ₖ ∈ p → ⟨x, z⟩ₖ ∈ q → y = z := by
    intro p q hp hq x y z hxy hxz
    obtain ⟨r, hr, hpr, hqr⟩ := hF.2.2.1 p q hp hq
    let : IsFunction r := ((mem_finitePartialFunctions _ _ _).mp (hF.1 r hr)).2.1
    exact IsFunction.unique (hpr _ hxy) (hqr _ hxz)
  refine ⟨?_, ?_⟩
  · intro a ha b hb _
    rcases le_total a.level b.level with hab | hba
    · exact Or.inl ⟨hab, FunctionTreeNode.subset_of_compatible
        (by simpa only [FunctionTreeNode.domain_graph] using C.monotone hab)
        (hcompat _ _ ha hb)⟩
    · exact Or.inr ⟨hba, FunctionTreeNode.subset_of_compatible
        (by simpa only [FunctionTreeNode.domain_graph] using C.monotone hba)
        (hcompat _ _ hb ha)⟩
  · intro i
    obtain ⟨p, hp, hdom⟩ := hcover i
    obtain ⟨_, hfun, _⟩ := (mem_finitePartialFunctions _ _ _).mp (hF.1 p hp)
    let := hfun
    have hpfun : p ∈ ((2 : ℕ) : V) ^ domain p :=
      mem_function_of_mem_function_of_subset (IsFunction.mem_function p)
        (finitePartialFunction_range (hF.1 p hp))
    exact ⟨⟨i, p ↾ (C.domain i), function_restrict_mem hpfun hdom⟩,
      hF.2.2.2 p _ hp (restrict_subset _ _), rfl⟩

theorem branchOfFilter_filterOfBranch {B : Set (FunctionTreeNode C)}
    (hB : (FunctionTreeNode.rankedTree (C := C)).IsBranch B) :
    branchOfFilter C (filterOfBranch C B) = B := Set.ext (filterOfBranch_graph_iff C hB)

/-- Covering filters are recovered from their tree branches. -/
theorem filterOfBranch_branchOfFilter {F : V → Prop} (hF : IsFunctionFilter (s := s) F)
    (hcover : ∀ i, ∃ p, F p ∧ C.domain i ⊆ domain p) :
    filterOfBranch C (branchOfFilter C F) = F := by
  funext p
  apply propext
  constructor
  · rintro ⟨_, a, ha, hpa⟩
    exact hF.2.2.2 a.graph p ha hpa
  · intro hp
    have hpP := hF.1 p hp
    obtain ⟨i, hi⟩ := C.cofinal (domain p) (finitePartialFunction_domain hpP)
      ((mem_finitePartialFunctions _ _ _).mp hpP).2.2
    obtain ⟨q, hq, hiq⟩ := hcover i
    obtain ⟨r, hr, hpr, hqr⟩ := hF.2.2.1 p q hp hq
    let : IsFunction r := ((mem_finitePartialFunctions _ _ _).mp (hF.1 r hr)).2.1
    have hir : C.domain i ⊆ domain r := by
      intro x hx
      obtain ⟨y, hxy⟩ := mem_domain_iff.mp (hiq x hx)
      exact mem_domain_of_kpair_mem (hqr _ hxy)
    have hrfun : r ∈ ((2 : ℕ) : V) ^ domain r :=
      mem_function_of_mem_function_of_subset (IsFunction.mem_function r)
        (finitePartialFunction_range (hF.1 r hr))
    let a : FunctionTreeNode C := ⟨i, r ↾ (C.domain i), function_restrict_mem hrfun hir⟩
    refine ⟨hpP, a, hF.2.2.2 r _ hr (restrict_subset _ _), ?_⟩
    intro z hz
    let : IsFunction p := ((mem_finitePartialFunctions _ _ _).mp hpP).2.1
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    exact kpair_mem_restrict_iff.mpr ⟨hpr _ hz, hi x (mem_domain_of_kpair_mem hz)⟩

/-- Every branch generates a maximal directed family in the entire finite-function poset. -/
theorem filterOfBranch_maximal {B : Set (FunctionTreeNode C)}
    (hB : (FunctionTreeNode.rankedTree (C := C)).IsBranch B)
    (F : V → Prop) (hFP : ∀ p, F p → p ∈ finitePartialFunctions s ((2 : ℕ) : V))
    (hFdir : ∀ p q, F p → F q → ∃ r, F r ∧ p ⊆ r ∧ q ⊆ r)
    (hBF : ∀ p, filterOfBranch C B p → F p) : ∀ p, F p → filterOfBranch C B p := by
  intro p hp
  have hpP := hFP p hp
  obtain ⟨i, hi⟩ := C.cofinal (domain p) (finitePartialFunction_domain hpP)
    ((mem_finitePartialFunctions _ _ _).mp hpP).2.2
  obtain ⟨a, ha, hlevel⟩ := hB.2 i
  change a.level = i at hlevel
  have haF := hBF a.graph ((filterOfBranch_graph_iff C hB a).mpr ha)
  obtain ⟨r, hr, hpr, har⟩ := hFdir p a.graph hp haF
  let : IsFunction p := ((mem_finitePartialFunctions _ _ _).mp hpP).2.1
  let : IsFunction r := ((mem_finitePartialFunctions _ _ _).mp (hFP r hr)).2.1
  refine ⟨hpP, a, ha, FunctionTreeNode.subset_of_compatible ?_ ?_⟩
  · rwa [FunctionTreeNode.domain_graph, hlevel]
  · intro x y z hxy hxz
    exact IsFunction.unique (hpr _ hxy) (har _ hxz)

/-- The branch ranks give a strictly increasing, cofinal chain in its filter. -/
theorem filterOfBranch_has_cofinal_chain {B : Set (FunctionTreeNode C)}
    (hB : (FunctionTreeNode.rankedTree (C := C)).IsBranch B) :
    ∃ p : I → V, (∀ i, filterOfBranch C B (p i)) ∧
      (∀ i j, i < j → p i ⊆ p j ∧ p i ≠ p j) ∧
      ∀ x, filterOfBranch C B x → ∃ i, x ⊆ p i := by
  refine ⟨fun i ↦ (hB.node i).graph, ?_, ?_, ?_⟩
  · intro i
    exact (filterOfBranch_graph_iff C hB _).mpr (hB.node_mem i)
  · intro i j hij
    refine ⟨(hB.node_monotone hij.le).2, ?_⟩
    intro heq
    have hnodes := FunctionTreeNode.graph_injective heq
    have hrank := congrArg (FunctionTreeNode.rankedTree (C := C)).rank hnodes
    rw [hB.rank_node, hB.rank_node] at hrank
    exact hij.ne hrank
  · rintro p ⟨_, a, ha, hpa⟩
    obtain ⟨i, hi⟩ := hB.node_cofinal a ha
    exact ⟨i, subset_trans hpa hi.2⟩

/-- Definability of the generated filters bounds the branch family without
assuming that the selected domain chain is definable in the original model. -/
theorem functionTree_branch_bound {I : Type u} [LinearOrder I]
    (C : FiniteDomainChain s I)
    (hfilters : ∀ B, (FunctionTreeNode.rankedTree (C := C)).IsBranch B →
      ℒₛₑₜ-predicate[V] (filterOfBranch C B))
    (hcard : Cardinal.mk V ≤ Cardinal.aleph 1) :
    Cardinal.mk {B : Set (FunctionTreeNode C) //
      (FunctionTreeNode.rankedTree (C := C)).IsBranch B} ≤ Cardinal.aleph 1 := by
  apply cardinal_definable_family_le_aleph_one
    (fun B : {B : Set (FunctionTreeNode C) //
      (FunctionTreeNode.rankedTree (C := C)).IsBranch B} ↦ filterOfBranch C B.val) _
    (fun B ↦ hfilters B.val B.property) hcard
  intro A B heq
  change filterOfBranch C A.val = filterOfBranch C B.val at heq
  apply Subtype.ext
  rw [← branchOfFilter_filterOfBranch C A.property,
    ← branchOfFilter_filterOfBranch C B.property, heq]

end ZFVP.Schmerl
