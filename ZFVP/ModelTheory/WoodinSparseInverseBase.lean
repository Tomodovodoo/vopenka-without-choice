import ZFVP.ModelTheory.WoodinRecodedInverse
import ZFVP.SetTheory.SparseInverseLimit
import ZFVP.SetTheory.WoodinSparseBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseInverseBase (θ c : V) : V :=
  sparseThreadCarrier θ θ (woodinSparseBounds θ) (forcingCodeP c) (forcingCodeUniverse c)

noncomputable def woodinSparseInverseOrder (θ c : V) : V :=
  sparseThreadOrder θ (woodinSparseBounds θ) (forcingCodeR c) (woodinSparseInverseBase θ c)

noncomputable def woodinSparseInverseFlatten (θ c : V) : V :=
  sparseThreadEncode θ (woodinSparseBounds θ) (forcingCodeP c) (forcingCodeUniverse c)

noncomputable def woodinSparseInverseBaseMap (θ c m : V) : V :=
  compose (woodinRecodedInverseBaseMap θ m) (woodinSparseInverseFlatten θ c)

instance woodinSparseInverseBase_definable : ℒₛₑₜ-function₂[V] woodinSparseInverseBase := by
  unfold woodinSparseInverseBase
  apply Language.DefinableFunction₅.comp <;> definability

instance woodinSparseInverseOrder_definable : ℒₛₑₜ-function₂[V] woodinSparseInverseOrder := by
  unfold woodinSparseInverseOrder
  apply Language.DefinableFunction₄.comp <;> definability

instance woodinSparseInverseFlatten_definable : ℒₛₑₜ-function₂[V] woodinSparseInverseFlatten := by
  unfold woodinSparseInverseFlatten
  apply Language.DefinableFunction₄.comp <;> definability

instance woodinSparseInverseBaseMap_definable : ℒₛₑₜ-function₃[V] woodinSparseInverseBaseMap := by
  unfold woodinSparseInverseBaseMap
  apply Language.DefinableFunction₂.comp (F := compose)
  · apply Language.DefinableFunction₂.comp (F := woodinRecodedInverseBaseMap) <;> definability
  · apply Language.DefinableFunction₂.comp (F := woodinSparseInverseFlatten) <;> definability

theorem mem_woodinSparseInverseBase_iff {θ c q : V} [IsOrdinal θ]
    (hc : IsForcingIterationCode θ c) :
    q ∈ woodinSparseInverseBase θ c ↔ IsSparseFunctionOn θ q ∧
      ∀ i ∈ θ, q ↾ (succ (woodinSourceIndex i)) ∈ (forcingCodeP c) ‘ i := by
  rw [woodinSparseInverseBase, mem_sparseThreadCarrier_iff hc.subset_universe (fun _ hx ↦ woodinSparseBounds_cover hx)]
  exact and_congr_right (fun _ ↦ forall_congr' (fun i ↦ forall_congr' (fun hi ↦ by
    rw [woodinSparseBounds_value hi])))

theorem woodinSparseInverse_threads {θ c : V} [IsOrdinal θ]
    (hsp : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
    (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i))) :
    forcingInverseCodePoset θ c = sparseRestrictionThreads θ (woodinSparseBounds θ)
      (forcingCodeP c) (forcingCodeUniverse c) := by
  apply forcingInverseLimit_eq_sparseRestrictionThreads
  · intro i hi p hp
    rw [woodinSparseBounds_value hi]
    exact hsp i hi p hp
  · intro i _ j hj hij
    exact woodinSparseBounds_mono hij hj
  · intro i hi j hj hij p hp
    rw [woodinSparseBounds_value hi]
    exact hπ i hi j hj hij p hp

theorem woodinSparseInverseFlatten_isomorphism {θ c : V} [IsOrdinal θ]
    (hc : IsForcingIterationCode θ c) (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hsp : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
    (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i))) :
    IsForcingIsomorphism (forcingInverseCodePoset θ c) (forcingInverseCodeOrder θ c)
      (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) (woodinSparseInverseFlatten θ c) := by
  unfold forcingInverseCodeOrder
  rw [woodinSparseInverse_threads hsp hπ]
  exact sparseThreadEncode_isomorphism hc.subset_universe
    (fun i hi ↦ woodinSparseBounds_limit_subset h0 hlim hi) (fun _ hx ↦ woodinSparseBounds_cover hx)

theorem woodinSparseInverseFlatten_value {θ c p : V} [IsOrdinal θ]
    (hsp : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
    (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)))
    (hp : p ∈ forcingInverseCodePoset θ c) : (woodinSparseInverseFlatten θ c) ‘ p = ⋃ˢ range p := by
  rw [woodinSparseInverse_threads hsp hπ] at hp
  exact sparseThreadEncode_value hp

theorem woodinSparseInverseFlatten_restrict {θ c p i : V} [IsOrdinal θ]
    (hsp : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
    (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)))
    (hp : p ∈ forcingInverseCodePoset θ c) (hi : i ∈ θ) :
    ((woodinSparseInverseFlatten θ c) ‘ p) ↾ (succ (woodinSourceIndex i)) = p ‘ i := by
  rw [woodinSparseInverseFlatten_value hsp hπ hp]
  rw [woodinSparseInverse_threads hsp hπ] at hp
  simpa only [woodinSparseBounds_value hi] using sparseRestrictionThread_union_restrict hp hi

theorem woodinSparseInverseBase_small {θ c δ : V}
    (hc : IsForcingIterationCode θ c) (hδ : IsChoicelessInaccessible δ) (hθ : θ ∈ hierarchy δ)
    (hP : ∀ i ∈ θ, (forcingCodeP c) ‘ i ∈ hierarchy δ) : woodinSparseInverseBase θ c ∈ hierarchy δ := by
  let := hδ.1
  have hfun := hc.tableP.mem_function hP
  have hU : forcingCodeUniverse c ∈ hierarchy δ := sUnion_mem_hierarchy_limit hδ.rankCriterion.2.2.1
    (hδ.rankCriterion.2.2.2.range_mem hδ.rankCriterion.2.2.1 hθ hfun)
  apply subset_mem_hierarchy_limit hδ.rankCriterion.2.2.1
    (power_mem_hierarchy_limit hδ.rankCriterion.2.2.1 (sUnion_mem_hierarchy_limit hδ.rankCriterion.2.2.1 hU))
  exact sparseThreadCarrier_subset _ _ _ _ _

end ZFVP
