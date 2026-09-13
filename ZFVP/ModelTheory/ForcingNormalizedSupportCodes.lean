import ZFVP.ModelTheory.ForcingNormalizedLimits
import ZFVP.SetTheory.ForcingMinimalSupportCodes

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingNormalizedSupportCodes (θ s m : V) : V :=
  forcingMinimalSupportCodes θ (forcingNormalizationCarriers θ s m)
    (forcingNormalizationSections θ s m) (forcingCodeUniverse s)

instance forcingNormalizedSupportCodes_definable : ℒₛₑₜ-function₃[V] forcingNormalizedSupportCodes := by
  have h : ℒₛₑₜ-relation₄[V] (fun C θ s m ↦ ∀ a, a ∈ C ↔ ∃ k ∈ θ, ∃ p ∈ forcingCodeUniverse s,
    a = ⟨k, p⟩ₖ ∧ IsMinimalSectionPoint (forcingNormalizationCarriers θ s m)
      (forcingNormalizationSections θ s m) k p) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingNormalizedSupportCodes (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingNormalizedSupportCodes, mem_forcingMinimalSupportCodes_iff]

noncomputable def forcingNormalizedSupportMap (θ s m : V) : V :=
  forcingMinimalSupportMap θ (forcingNormalizationCarriers θ s m)
    (forcingNormalizationProjections θ s m) (forcingNormalizationSections θ s m) (forcingCodeUniverse s)

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₅.comp

instance forcingNormalizedSupportMap_definable : ℒₛₑₜ-function₃[V] forcingNormalizedSupportMap := by
  have h : ℒₛₑₜ-relation₄[V] (fun g θ s m ↦ ∀ z, z ∈ g ↔ ∃ a ∈ forcingNormalizedSupportCodes θ s m,
    z = ⟨a, forcingSectionThread θ (forcingNormalizationProjections θ s m)
      (forcingNormalizationSections θ s m) (kpair.π₁ a) (kpair.π₂ a)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingNormalizedSupportMap (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingNormalizedSupportMap, forcingMinimalSupportMap, mem_definableGraph_iff,
    forcingMinimalSupportDecode, forcingNormalizedSupportCodes]

noncomputable def forcingNormalizedSupportOrder (θ s m : V) : V :=
  forcingPullbackOrder (forcingNormalizedSupportCodes θ s m)
    (forcingOrderRestriction
      (forcingMapFixedPoints ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)
        (forcingNormalizationDirectMap θ s m))
      ((forcingCodeR (forcingDirectCode θ s)) ‘ θ))
    (forcingNormalizedSupportMap θ s m)

instance forcingNormalizedSupportOrder_definable : ℒₛₑₜ-function₃[V] forcingNormalizedSupportOrder := by
  have h : ℒₛₑₜ-relation₄[V] (fun R θ s m ↦ ∀ z, z ∈ R ↔
    z ∈ (forcingNormalizedSupportCodes θ s m) ×ˢ (forcingNormalizedSupportCodes θ s m) ∧
    ⟨(forcingNormalizedSupportMap θ s m) ‘ (kpair.π₁ z),
      (forcingNormalizedSupportMap θ s m) ‘ (kpair.π₂ z)⟩ₖ ∈
      forcingOrderRestriction (forcingMapFixedPoints ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)
        (forcingNormalizationDirectMap θ s m)) ((forcingCodeR (forcingDirectCode θ s)) ‘ θ)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingNormalizedSupportOrder (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingNormalizedSupportOrder, forcingPullbackOrder, mem_sep_iff]

variable {θ s m : V} [IsOrdinal θ]
  (h : IsForcingNormalizationFamily θ s m) (hs : IsForcingIterationCode θ s)

include h hs in
theorem forcingNormalizedSupportMap_isomorphism :
    IsForcingIsomorphism (forcingNormalizedSupportCodes θ s m) (forcingNormalizedSupportOrder θ s m)
      (forcingMapFixedPoints ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)
        (forcingNormalizationDirectMap θ s m))
      (forcingOrderRestriction
        (forcingMapFixedPoints ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)
          (forcingNormalizationDirectMap θ s m))
        ((forcingCodeR (forcingDirectCode θ s)) ‘ θ)) (forcingNormalizedSupportMap θ s m) := by
  have hU : ∀ i ∈ θ, (forcingNormalizationCarriers θ s m) ‘ i ⊆ forcingCodeUniverse s :=
    fun i hi p hp ↦ hs.subset_universe i hi p (h.inclusion i hi p hp)
  unfold forcingNormalizedSupportCodes forcingNormalizedSupportOrder forcingNormalizedSupportMap
  rw [forcingNormalized_direct_fixedPoints h hs]
  exact forcingMinimalSupportMap_isomorphism (forcingNormalized_split h hs) hU

include h hs in
theorem forcingNormalizedSupportOrder_preorder :
    IsForcingPreorder (forcingNormalizedSupportCodes θ s m) (forcingNormalizedSupportOrder θ s m) := by
  have hD : IsForcingPreorder ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)
      ((forcingCodeR (forcingDirectCode θ s)) ‘ θ) := by
    simpa only [forcingDirectCode, forcingThreadCode_poset, forcingThreadCode_order] using
      forcingDirectLimit_preorder hs.system.order.preorder (U := forcingCodeUniverse s)
  apply forcingPullbackOrder_preorder
    (forcingOrderRestriction_preorder hD (fun p hp ↦ (mem_sep_iff.mp hp).1))
  exact (forcingNormalizedSupportMap_isomorphism h hs).1

include h in
theorem forcingNormalizedSupportCodes_subset_hierarchy
    (hlim : ∀ α ∈ θ, succ α ∈ θ)
    (hP : ∀ i ∈ θ, (forcingCodeP s) ‘ i ∈ hierarchy θ) :
    forcingNormalizedSupportCodes θ s m ⊆ hierarchy θ := by
  apply forcingMinimalSupportCodes_subset_hierarchy hlim
  intro i hi
  exact subset_mem_hierarchy_limit hlim (hP i hi) (h.inclusion i hi)

include h in
theorem forcingNormalizedSupportOrder_subset_hierarchy
    (hlim : ∀ α ∈ θ, succ α ∈ θ)
    (hP : ∀ i ∈ θ, (forcingCodeP s) ‘ i ∈ hierarchy θ) :
    forcingNormalizedSupportOrder θ s m ⊆ hierarchy θ := by
  intro z hz
  unfold forcingNormalizedSupportOrder forcingPullbackOrder at hz
  have hz' : z ∈ (forcingNormalizedSupportCodes θ s m) ×ˢ (forcingNormalizedSupportCodes θ s m) :=
    (mem_sep_iff.mp hz).1
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz'
  exact kpair_mem_hierarchy_limit hlim
    (forcingNormalizedSupportCodes_subset_hierarchy h hlim hP a ha)
    (forcingNormalizedSupportCodes_subset_hierarchy h hlim hP b hb)

end ZFVP
