import ZFVP.ModelTheory.ForcingNormalizationFamily
import ZFVP.SetTheory.FunctionComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingNormalizationOrders (θ s m : V) : V :=
  definableGraph θ (fun i ↦ forcingOrderRestriction ((forcingNormalizationCarriers θ s m) ‘ i)
    ((forcingCodeR s) ‘ i)) (by definability)

noncomputable def forcingNormalizationProjections (θ s m : V) : V :=
  definableGraph (θ ×ˢ θ) (fun z ↦ ((forcingCodeπ s) ‘ z) ↾
    ((forcingNormalizationCarriers θ s m) ‘ (kpair.π₂ z))) (by definability)

noncomputable def forcingNormalizationSections (θ s m : V) : V :=
  definableGraph (θ ×ˢ θ) (fun z ↦ ((forcingCodeE s) ‘ z) ↾
    ((forcingNormalizationCarriers θ s m) ‘ (kpair.π₁ z))) (by definability)

/-- Specify the values of a source map on a supplied domain. -/
noncomputable def forcingMapOn (A f : V) : V := definableGraph A (fun p ↦ f ‘ p) (by definability)

instance forcingMapOn_definable : ℒₛₑₜ-function₂[V] forcingMapOn := by
  have h : ℒₛₑₜ-relation₃[V] (fun g A f ↦ ∀ z, z ∈ g ↔ ∃ p ∈ A, z = ⟨p, f ‘ p⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingMapOn (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [forcingMapOn, mem_definableGraph_iff]

theorem forcingMapOn_value {A f p : V} (hp : p ∈ A) : (forcingMapOn A f) ‘ p = f ‘ p :=
  value_definableGraph _ _ _ hp

noncomputable def forcingNormalizationLifts (θ s m : V) : V :=
  definableGraph (θ ×ˢ θ) (fun z ↦ forcingMapOn
    (((forcingNormalizationCarriers θ s m) ‘ (kpair.π₂ z)) ×ˢ
      ((forcingNormalizationCarriers θ s m) ‘ (kpair.π₁ z))) ((forcingCodeL s) ‘ z)) (by definability)

/-- Restrict the actual source maps to the normalized carriers. -/
noncomputable def forcingNormalizedCode (θ s m : V) : V :=
  forcingIterationCode (forcingNormalizationCarriers θ s m) (forcingNormalizationOrders θ s m)
    (forcingNormalizationProjections θ s m) (forcingNormalizationSections θ s m)
    (forcingNormalizationLifts θ s m) (forcingCodet s)

instance forcingNormalizationOrders_definable : ℒₛₑₜ-function₃[V] forcingNormalizationOrders := by
  have h : ℒₛₑₜ-relation₄[V] (fun g θ s m ↦ ∀ w, w ∈ g ↔ ∃ i ∈ (θ),
    w = ⟨i, forcingOrderRestriction ((forcingNormalizationCarriers θ s m) ‘ i) ((forcingCodeR s) ‘ i)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingNormalizationOrders (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingNormalizationOrders, mem_definableGraph_iff]

instance forcingNormalizationProjections_definable : ℒₛₑₜ-function₃[V] forcingNormalizationProjections := by
  have h : ℒₛₑₜ-relation₄[V] (fun g θ s m ↦ ∀ w, w ∈ g ↔ ∃ z ∈ (θ ×ˢ θ),
    w = ⟨z, ((forcingCodeπ s) ‘ z) ↾ ((forcingNormalizationCarriers θ s m) ‘ (kpair.π₂ z))⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingNormalizationProjections (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingNormalizationProjections, mem_definableGraph_iff]

instance forcingNormalizationSections_definable : ℒₛₑₜ-function₃[V] forcingNormalizationSections := by
  have h : ℒₛₑₜ-relation₄[V] (fun g θ s m ↦ ∀ w, w ∈ g ↔ ∃ z ∈ (θ ×ˢ θ),
    w = ⟨z, ((forcingCodeE s) ‘ z) ↾ ((forcingNormalizationCarriers θ s m) ‘ (kpair.π₁ z))⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingNormalizationSections (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingNormalizationSections, mem_definableGraph_iff]

instance forcingNormalizationLifts_definable : ℒₛₑₜ-function₃[V] forcingNormalizationLifts := by
  have h : ℒₛₑₜ-relation₄[V] (fun g θ s m ↦ ∀ w, w ∈ g ↔ ∃ z ∈ (θ ×ˢ θ),
    w = ⟨z, forcingMapOn (((forcingNormalizationCarriers θ s m) ‘ (kpair.π₂ z)) ×ˢ ((forcingNormalizationCarriers θ s m) ‘ (kpair.π₁ z))) ((forcingCodeL s) ‘ z)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingNormalizationLifts (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingNormalizationLifts, mem_definableGraph_iff]

instance forcingNormalizedCode_definable : ℒₛₑₜ-function₃[V] forcingNormalizedCode := by
  unfold forcingNormalizedCode forcingIterationCode
  definability

variable {θ s m i j : V}
local notation "N" => forcingNormalizationCarriers θ s m

theorem forcingNormalizationOrders_value (hi : i ∈ θ) :
    (forcingNormalizationOrders θ s m) ‘ i = forcingOrderRestriction (N ‘ i) ((forcingCodeR s) ‘ i) :=
  value_definableGraph _ _ _ hi

theorem forcingNormalizationProjections_value (hi : i ∈ θ) (hj : j ∈ θ) :
    (forcingNormalizationProjections θ s m) ‘ ⟨i, j⟩ₖ = ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ↾ (N ‘ j) := by
  rw [forcingNormalizationProjections, value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hi, hj⟩), kpair.π₂_kpair]

theorem forcingNormalizationSections_value (hi : i ∈ θ) (hj : j ∈ θ) :
    (forcingNormalizationSections θ s m) ‘ ⟨i, j⟩ₖ = ((forcingCodeE s) ‘ ⟨i, j⟩ₖ) ↾ (N ‘ i) := by
  rw [forcingNormalizationSections, value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hi, hj⟩), kpair.π₁_kpair]

theorem forcingNormalizationLifts_value (hi : i ∈ θ) (hj : j ∈ θ) :
    (forcingNormalizationLifts θ s m) ‘ ⟨i, j⟩ₖ = forcingMapOn ((N ‘ j) ×ˢ (N ‘ i))
      ((forcingCodeL s) ‘ ⟨i, j⟩ₖ) := by
  rw [forcingNormalizationLifts, value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hi, hj⟩),
    kpair.π₁_kpair, kpair.π₂_kpair]

theorem forcingNormalizationLifts_apply (hi : i ∈ θ) (hj : j ∈ θ) {a b : V}
    (ha : a ∈ N ‘ j) (hb : b ∈ N ‘ i) :
    ((forcingNormalizationLifts θ s m) ‘ ⟨i, j⟩ₖ) ‘ ⟨a, b⟩ₖ =
      ((forcingCodeL s) ‘ ⟨i, j⟩ₖ) ‘ ⟨a, b⟩ₖ := by
  rw [forcingNormalizationLifts_value hi hj, forcingMapOn_value (kpair_mem_iff.mpr ⟨ha, hb⟩)]

theorem IsForcingNormalizationFamily.projection_mem [IsOrdinal θ]
    (h : IsForcingNormalizationFamily θ s m) (hs : IsForcingIterationCode θ s)
    (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j) {p : V} (hp : p ∈ N ‘ j) :
    ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ p ∈ N ‘ i := by
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  have hpP := h.inclusion j hj p hp
  rcases IsOrdinal.subset_iff.mp hij with rfl | hij
  · have hh := hs.system.split.retraction i hi i hi (subset_refl _) p hpP
    rw [hs.system.split.secId i hi p hpP] at hh
    rwa [hh]
  · rw [forcingNormalizationCarriers_value hi]
    refine mem_sep_iff.mpr ⟨hs.system.split.projMaps i hi j hj (IsOrdinal.toIsTransitive.transitive _ hij) p hpP, ?_⟩
    have hh := h.projection j hj i hij hi p hpP
    rw [h.fixes j hj p hp] at hh
    exact hh.symm

theorem IsForcingNormalizationFamily.section_mem
    (h : IsForcingNormalizationFamily θ s m) (hs : IsForcingIterationCode θ s)
    (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j) {p : V} (hp : p ∈ N ‘ i) :
    ((forcingCodeE s) ‘ ⟨i, j⟩ₖ) ‘ p ∈ N ‘ j := by
  have hpP := h.inclusion i hi p hp
  rw [forcingNormalizationCarriers_value hj]
  refine mem_sep_iff.mpr ⟨hs.system.split.secMaps i hi j hj hij p hpP, ?_⟩
  rw [h.sectionCoherent i hi j hj hij p hpP, h.fixes i hi p hp]

theorem forcingNormalizationProjections_apply
    (h : IsForcingNormalizationFamily θ s m) (hs : IsForcingIterationCode θ s)
    (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j) {p : V} (hp : p ∈ N ‘ j) :
    ((forcingNormalizationProjections θ s m) ‘ ⟨i, j⟩ₖ) ‘ p = ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ p := by
  have hf := hs.system.functions.projection i hi j hj hij
  let := IsFunction.of_mem hf
  rw [forcingNormalizationProjections_value hi hj]
  exact value_restrict ((domain_eq_of_mem_function hf).symm ▸ h.inclusion j hj p hp) hp

theorem forcingNormalizationSections_apply
    (h : IsForcingNormalizationFamily θ s m) (hs : IsForcingIterationCode θ s)
    (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j) {p : V} (hp : p ∈ N ‘ i) :
    ((forcingNormalizationSections θ s m) ‘ ⟨i, j⟩ₖ) ‘ p = ((forcingCodeE s) ‘ ⟨i, j⟩ₖ) ‘ p := by
  have hf := hs.system.functions.sectionMap i hi j hj hij
  let := IsFunction.of_mem hf
  rw [forcingNormalizationSections_value hi hj]
  exact value_restrict ((domain_eq_of_mem_function hf).symm ▸ h.inclusion i hi p hp) hp

end ZFVP
