import ZFVP.ModelTheory.SchmerlFunctionTree
import ZFVP.ModelTheory.SchmerlClassTree
import ZFVP.SetTheory.EndExtensionLevyCollapse
import ZFVP.SetTheory.EndExtensionSubsetCoding
import ZFVP.ModelTheory.EndExtensionBasics

/-! The end-extension use of the selected finite-function trees. A binary
function in an end extension gives a branch because every restriction to an
old internally finite domain is old. Definability of the full filter generated
by that branch then recovers the entire function in the original model.
-/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u v w

variable {V : Type u} {W : Type w}
  [SetStructure V] [SetStructure W] [Nonempty V] [Nonempty W]
  [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  {I : Type v} [LinearOrder I] {s : V} (C : FiniteDomainChain s I)
  (j : MembershipEndExtension V W)

/-- The trace on old tree nodes of a binary function in an end extension. -/
def functionTraceBranch (χ : W) : Set (FunctionTreeNode C) :=
  {a | j a.graph ⊆ χ}

/-- Every finite-domain restriction of the new function is an old tree node. -/
theorem exists_functionTraceBranch_node {χ : W}
    (hχ : χ ∈ ((2 : ℕ) : W) ^ j s) (i : I) :
    ∃ a : FunctionTreeNode C, a.level = i ∧
      j a.graph = χ ↾ (j (C.domain i)) := by
  have hdsub : j (C.domain i) ⊆ j s := (j.subset_iff _ _).mpr (C.subset i)
  have hrfun := function_restrict_mem hχ hdsub
  let : IsFunction (χ ↾ (j (C.domain i))) := IsFunction.of_mem hrfun
  have hrfin : IsInternallyFinite (χ ↾ (j (C.domain i))) :=
    internallyFinite_function (by
      rw [domain_eq_of_mem_function hrfun]
      exact j.map_internallyFinite (C.finite i))
  have hrsub : χ ↾ (j (C.domain i)) ⊆ j (s ×ˢ ((2 : ℕ) : V)) := by
    rw [j.map_prod, j.map_numeral]
    exact subset_trans (restrict_subset _ _) (subset_prod_of_mem_function hχ)
  obtain ⟨p, _, heq⟩ := j.exists_eq_map_of_finite_subset hrsub hrfin
  have hp : p ∈ ((2 : ℕ) : V) ^ C.domain i := by
    apply (j.function_iff _ _ _).mp
    rw [j.map_numeral, ← heq]
    exact hrfun
  exact ⟨⟨i, p, hp⟩, rfl, heq.symm⟩

/-- The trace is a full branch, with no maximal-filter coverage assumption. -/
theorem functionTraceBranch_isBranch {χ : W} (hχ : χ ∈ ((2 : ℕ) : W) ^ j s) :
    (FunctionTreeNode.rankedTree (C := C)).IsBranch (functionTraceBranch C j χ) := by
  let : IsFunction χ := IsFunction.of_mem hχ
  have hcomp (a b : FunctionTreeNode C) (ha : a ∈ functionTraceBranch C j χ)
      (hb : b ∈ functionTraceBranch C j χ) :
      ∀ x y z, ⟨x, y⟩ₖ ∈ a.graph → ⟨x, z⟩ₖ ∈ b.graph → y = z := by
    intro x y z hxy hxz
    apply j.injective
    apply IsFunction.unique (f := χ)
    · apply ha
      rw [← j.map_kpair]
      exact (j.mem_iff _ _).mpr hxy
    · apply hb
      rw [← j.map_kpair]
      exact (j.mem_iff _ _).mpr hxz
  refine ⟨?_, ?_⟩
  · intro a ha b hb _
    rcases le_total a.level b.level with hab | hba
    · exact Or.inl ⟨hab, FunctionTreeNode.subset_of_compatible
        (by simpa only [FunctionTreeNode.domain_graph] using C.monotone hab) (hcomp a b ha hb)⟩
    · exact Or.inr ⟨hba, FunctionTreeNode.subset_of_compatible
        (by simpa only [FunctionTreeNode.domain_graph] using C.monotone hba) (hcomp b a hb ha)⟩
  · intro i
    obtain ⟨a, hai, haχ⟩ := exists_functionTraceBranch_node C j hχ i
    exact ⟨a, by change j a.graph ⊆ χ; rw [haχ]; exact restrict_subset _ _, hai⟩

/-- A definable full trace filter codes the whole binary function in the old model.
The selected domain predicate itself need not be definable in that model. -/
theorem exists_eq_map_of_functionTraceFilter_definable {χ : W}
    (hχ : χ ∈ ((2 : ℕ) : W) ^ j s)
    (hdef : ℒₛₑₜ-predicate[V] (filterOfBranch C (functionTraceBranch C j χ))) :
    ∃ f : V, j f = χ := by
  let B := functionTraceBranch C j χ
  let P : V → Prop := filterOfBranch C B
  let m : V := sep (finitePartialFunctions s ((2 : ℕ) : V)) P hdef
  have hm (p : V) : p ∈ m ↔ filterOfBranch C B p := by
    rw [mem_sep_iff]
    constructor
    · exact fun h ↦ h.2
    · intro hp
      exact ⟨hp.1, hp⟩
  refine ⟨⋃ˢ m, ?_⟩
  rw [j.map_sUnion]
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨p, hp, hzp⟩ := mem_sUnion_iff.mp hz
    obtain ⟨q, hq, rfl⟩ := j.endExtension m p hp
    obtain ⟨_, a, ha, hqa⟩ := (hm q).mp hq
    exact ha _ (((j.subset_iff _ _).mpr hqa) _ hzp)
  · intro hz
    let : IsFunction χ := IsFunction.of_mem hχ
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    have hxs : x ∈ j s := (mem_of_mem_functions hχ hz).1
    obtain ⟨x₀, hx₀, rfl⟩ := j.endExtension s x hxs
    have hsingleton : IsInternallyFinite ({x₀} : V) := by
      simpa using internallyFinite_insert (internallyFinite_empty (V := V)) x₀
    obtain ⟨i, hi⟩ := C.cofinal ({x₀} : V) (singleton_subset_iff_mem.mpr hx₀) hsingleton
    have hxCi : x₀ ∈ C.domain i := hi x₀ (mem_singleton_iff.mpr rfl)
    obtain ⟨a, _, haχ⟩ := exists_functionTraceBranch_node C j hχ i
    have haB : a ∈ B := by
      change j a.graph ⊆ χ
      rw [haχ]
      exact restrict_subset _ _
    refine mem_sUnion_iff.mpr ⟨j a.graph,
      (j.mem_iff _ _).mpr ((hm _).mpr
        ⟨a.graph_mem_finitePartialFunctions, a, haB, subset_refl _⟩), ?_⟩
    rw [haχ]
    exact kpair_mem_restrict_iff.mpr ⟨hz, (j.mem_iff _ _).mpr hxCi⟩

/-- Definability of branch-generated filters prevents new binary functions
on the domain in any ZF end extension. -/
theorem function_closed_of_functionTree_filters_definable
    (hfilters : ∀ B : Set (FunctionTreeNode C),
      (FunctionTreeNode.rankedTree (C := C)).IsBranch B →
      ℒₛₑₜ-predicate[V] (filterOfBranch C B))
    {χ : W} (hχ : χ ∈ ((2 : ℕ) : W) ^ j s) :
    ∃ f ∈ ((2 : ℕ) : V) ^ s, j f = χ := by
  obtain ⟨f, hf⟩ := exists_eq_map_of_functionTraceFilter_definable C j hχ
    (hfilters _ (functionTraceBranch_isBranch C j hχ))
  refine ⟨f, (j.function_iff _ _ _).mp ?_, hf⟩
  rw [j.map_numeral, hf]
  exact hχ

/-- The selected function tree also prevents new subsets of its domain. -/
theorem subset_closed_of_functionTree_filters_definable
    (hfilters : ∀ B : Set (FunctionTreeNode C),
      (FunctionTreeNode.rankedTree (C := C)).IsBranch B →
      ℒₛₑₜ-predicate[V] (filterOfBranch C B))
    {Y : W} (hY : Y ⊆ j s) : ∃ Z, Z ⊆ s ∧ j Z = Y := by
  have htwo : ((2 : ℕ) : V) = doubleton ∅ (doubleton ∅ ∅) := by
    apply mem_ext
    intro x
    have hone : (1 : V) = doubleton ∅ ∅ := by
      apply mem_ext
      intro y
      simp [one_def, zero_def]
    simp [hone, zero_def]
  apply j.subset_of_function_closed ?_ hY
  intro χ hχ
  rw [← htwo, j.map_numeral] at hχ
  obtain ⟨f, hf, heq⟩ := function_closed_of_functionTree_filters_definable C j hfilters hχ
  exact ⟨f, htwo ▸ hf, heq⟩

/-- Definability of the generated filters on each internally infinite domain yields powerset
preservation for every ZF end extension. Internally finite domains use the
independently proved finite-subset absoluteness theorem. -/
theorem powersetPreserving_of_functionTree_filters_definable
    (hfilters : ∀ s : V, IsInternallyInfinite s →
      ∃ C : FiniteDomainChain s (Ordinal.ToType (Ordinal.omega.{u} 1)),
        ∀ B : Set (FunctionTreeNode C),
          (FunctionTreeNode.rankedTree (C := C)).IsBranch B →
          ℒₛₑₜ-predicate[V] (filterOfBranch C B)) :
    j.IsPowersetPreserving := by
  classical
  intro s Y hY
  by_cases hs : IsInternallyFinite s
  · obtain ⟨Z, _, hZ⟩ := j.exists_eq_map_of_finite_subset hY
      (internallyFinite_subset (j.map_internallyFinite hs) hY)
    exact ⟨Z, hZ.symm⟩
  · obtain ⟨C, hC⟩ := hfilters s hs
    obtain ⟨Z, _, hZ⟩ := subset_closed_of_functionTree_filters_definable C j hC hY
    exact ⟨Z, hZ⟩

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
/-- In a powerset-preserving end extension, every definable predicate has an
amenable trace on the original model. -/
theorem definable_trace_amenable (hpower : j.IsPowersetPreserving)
    {X : W → Prop} (hX : ℒₛₑₜ-predicate[W] X) :
    IsAmenableClass V (fun x ↦ X (j x)) := by
  intro a
  let b : W := sep (j a) X hX
  have hb : b ⊆ j a := fun _ hx ↦ (mem_sep_iff.mp hx).1
  obtain ⟨c, hc⟩ := hpower a b hb
  refine ⟨c, fun x ↦ ?_⟩
  rw [← j.mem_iff, hc]
  change j x ∈ sep (j a) X hX ↔ x ∈ a ∧ X (j x)
  rw [mem_sep_iff, j.mem_iff]

/-- Rather classlessness and the selected-tree hypothesis make all ZF end
extensions conservative, which is the endgame needed in Theorem 5.18. -/
theorem definable_trace_of_classlessness_and_functionTree_filters
    (hclasses : ∀ X : V → Prop, IsAmenableClass V X → ℒₛₑₜ-predicate[V] X)
    (hfilters : ∀ s : V, IsInternallyInfinite s →
      ∃ C : FiniteDomainChain s (Ordinal.ToType (Ordinal.omega.{u} 1)),
        ∀ B : Set (FunctionTreeNode C),
          (FunctionTreeNode.rankedTree (C := C)).IsBranch B →
          ℒₛₑₜ-predicate[V] (filterOfBranch C B))
    {X : W → Prop} (hX : ℒₛₑₜ-predicate[W] X) :
    ℒₛₑₜ-predicate[V] (fun x ↦ X (j x)) :=
  hclasses _ (definable_trace_amenable j
    (powersetPreserving_of_functionTree_filters_definable j hfilters) hX)

end ZFVP.Schmerl
