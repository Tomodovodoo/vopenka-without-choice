import ZFVP.ModelTheory.WoodinFixedPointDirect
import ZFVP.ModelTheory.WoodinStageNameCoding

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {δ γ : V} (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V)
  (hγ : γ ∈ δ) (hfix : (kpair.π₂ (woodinIterationRec δ)) ‘ γ = γ)
include hδ hAC hγ hfix

theorem woodinIteration_fixedPoint_prefix_extends :
    ForcingCodeExtends (woodinIterationPrefix γ) (kpair.π₁ (woodinIterationRec δ)) := by
  have he : ForcingCodeExtends (woodinIterationPrefix γ) (kpair.π₁ (woodinIterationRec γ)) := by
    rw [woodinIteration_fixedPoint_direct hδ hAC hγ hfix, kpair.π₁_kpair]
    exact forcingThreadCode_extends (woodinIteration_fixedPoint_prefix hδ hAC hγ hfix).code _
  exact he.trans (woodinIteration_fixedPoint_extends hδ hAC hγ).1

theorem woodinStageCarrier_fixedPoint_subset : woodinStageCarrier γ ⊆ hierarchy γ := by
  have hi := woodinIteration_fixedPoint_inaccessible hδ hAC hγ hfix
  let := hi.1
  have h := woodinIteration_fixedPoint_prefix hδ hAC hγ hfix
  apply forcingStageConditions_subset_hierarchy hi.rankCriterion.2.2.1
  intro i hi' p hp
  have hs := h.small i hi' γ hi
  simp only [woodinIterationStage, woodinStagePoset_code, woodinStageCardinal_code] at hs
  exact (hierarchy_transitive γ).mem_trans hp (hs (h.bounded i hi'))

theorem woodinStageMap_fixedPoint_maps :
    woodinStageMap γ ∈ ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ γ) ^ woodinStageCarrier γ := by
  have hi := woodinIteration_fixedPoint_inaccessible hδ hAC hγ hfix
  let := hi.1
  rw [woodinIteration_fixedPoint_poset hδ hAC hγ hfix]
  have h := (woodinIteration_fixedPoint_prefix hδ hAC hγ hfix).code
  exact forcingStageThreadMap_maps h.system.split h.subset_universe

theorem woodinStageMap_fixedPoint_surjective {p : V}
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ γ) :
    ∃ z ∈ woodinStageCarrier γ, (woodinStageMap γ) ‘ z = p := by
  have hi := woodinIteration_fixedPoint_inaccessible hδ hAC hγ hfix
  let := hi.1
  rw [woodinIteration_fixedPoint_poset hδ hAC hγ hfix] at hp
  have h := (woodinIteration_fixedPoint_prefix hδ hAC hγ hfix).code
  exact forcingStageThreadMap_surjective h.system.split h.subset_universe hp

theorem woodinLocalOrderOn_fixedPoint_pullback :
    woodinLocalOrderOn (woodinStageCarrier γ) = forcingPullbackOrder (woodinStageCarrier γ)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ γ) (woodinStageMap γ) := by
  let := hδ.inaccessible.1
  let := (woodinIteration_fixedPoint_inaccessible hδ hAC hγ hfix).1
  rw [woodinIteration_fixedPoint_order hδ hAC hγ hfix]
  exact woodinLocalOrderOn_eq_pullback (fun _ hi ↦
    ((woodinIterationExit hδ hAC).2.1 _ (IsOrdinal.toIsTransitive.mem_trans hi hγ)).1)

theorem woodinIteration_fixedPoint_section {i : V} (hi : i ∈ γ) :
    (forcingCodeE (kpair.π₁ (woodinIterationRec δ))) ‘ ⟨i, γ⟩ₖ =
      forcingThreadSection γ (forcingCodeP (woodinIterationPrefix γ))
        (forcingCodeπ (woodinIterationPrefix γ)) (forcingCodeE (woodinIterationPrefix γ)) i := by
  have hc := ((woodinIterationExit hδ hAC).2.1 γ hγ).1.code
  rw [← hc.tableE.value_of_subset (woodinIteration_endpoint_valid hδ hAC).1.code.tableE
    (woodinIteration_fixedPoint_extends hδ hAC hγ).1.subE
    (mem_prod_iff.mpr ⟨i, mem_succ_iff.mpr (Or.inr hi), γ, mem_succ_self γ, rfl⟩)]
  rw [woodinIteration_fixedPoint_direct hδ hAC hγ hfix, kpair.π₁_kpair]
  simp only [forcingDirectCode, forcingThreadCode, forcingIterationCodeNext,
    forcingCodeE_code, forcingMatrixNext_column hi, forcingLimitSectionColumn_value hi]

theorem woodinStageMap_fixedPoint_value {i p : V} (hz : ⟨i, p⟩ₖ ∈ woodinStageCarrier γ) :
    (woodinStageMap γ) ‘ ⟨i, p⟩ₖ =
      ((forcingCodeE (kpair.π₁ (woodinIterationRec δ))) ‘ ⟨i, γ⟩ₖ) ‘ p := by
  let := (woodinIteration_fixedPoint_inaccessible hδ hAC hγ hfix).1
  have hz' := (kpair_mem_forcingStageConditions_iff _ _ _ _ _).mp hz
  rw [woodinIteration_fixedPoint_section hδ hAC hγ hfix hz'.1]
  simp only [woodinStageMap, forcingStageThreadMap_value hz, kpair.π₁_kpair, kpair.π₂_kpair]
  exact (forcingThreadSection_value hz'.2.2).symm

theorem woodinIteration_fixedPoint_earlier_poset_small {i : V} (hi : i ∈ γ) :
    (forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ i ∈ hierarchy γ := by
  let := hδ.inaccessible.1
  have hg := woodinIteration_fixedPoint_inaccessible hδ hAC hγ hfix
  have h := (woodinIteration_endpoint_valid hδ hAC).1
  have hi' : i ∈ succ δ := mem_succ_iff.mpr (Or.inr (IsOrdinal.toIsTransitive.mem_trans hi hγ))
  have hb := h.increasing i hi' γ (mem_succ_iff.mpr (Or.inr hγ)) hi
  rw [hfix] at hb
  have hs := h.small i hi' γ hg
  simp only [woodinIterationStage, woodinStagePoset_code, woodinStageCardinal_code] at hs
  exact hs hb

theorem woodinStageCarrier_fixedPoint_tag_mem {i p : V} (hi : i ∈ γ)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ i) :
    ⟨i, p⟩ₖ ∈ woodinStageCarrier γ := by
  let := (woodinIteration_fixedPoint_inaccessible hδ hAC hγ hfix).1
  have h := (woodinIteration_fixedPoint_prefix hδ hAC hγ hfix).code
  have hp' : p ∈ (forcingCodeP (woodinIterationPrefix γ)) ‘ i := by
    rwa [h.tableP.value_of_subset (woodinIteration_endpoint_valid hδ hAC).1.code.tableP
      (woodinIteration_fixedPoint_prefix_extends hδ hAC hγ hfix).subP hi]
  exact (kpair_mem_forcingStageConditions_iff _ _ _ _ _).mpr
    ⟨hi, h.subset_universe i hi p hp', hp'⟩

theorem woodinStageTag_fixedPoint_maps {i : V} (hi : i ∈ γ) :
    woodinStageTag δ i ∈ (woodinStageCarrier γ) ^
      ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ i) :=
  definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun _ hp ↦ woodinStageCarrier_fixedPoint_tag_mem hδ hAC hγ hfix hi hp)

theorem woodinStageTag_fixedPoint_mem_hierarchy {i : V} (hi : i ∈ γ) :
    woodinStageTag δ i ∈ hierarchy γ :=
  (woodinIteration_fixedPoint_inaccessible hδ hAC hγ hfix).function_mem
    (woodinIteration_fixedPoint_earlier_poset_small hδ hAC hγ hfix hi)
    (mem_function_of_mem_function_of_subset (woodinStageTag_fixedPoint_maps hδ hAC hγ hfix hi)
      (woodinStageCarrier_fixedPoint_subset hδ hAC hγ hfix))

theorem woodinStageTag_compose_fixedPoint {i : V} (hi : i ∈ γ) :
    compose (woodinStageTag δ i) (woodinStageMap γ) =
      (forcingCodeE (kpair.π₁ (woodinIterationRec δ))) ‘ ⟨i, γ⟩ₖ := by
  let := hδ.inaccessible.1
  let := (woodinIteration_fixedPoint_inaccessible hδ hAC hγ hfix).1
  have ht := woodinStageTag_fixedPoint_maps hδ hAC hγ hfix hi
  have hm := woodinStageMap_fixedPoint_maps hδ hAC hγ hfix
  have he := (woodinIteration_endpoint_valid hδ hAC).1.code.system.functions.sectionMap
    i (mem_succ_iff.mpr (Or.inr (IsOrdinal.toIsTransitive.mem_trans hi hγ)))
    γ (mem_succ_iff.mpr (Or.inr hγ)) (IsOrdinal.toIsTransitive.transitive _ hi)
  let := IsFunction.of_mem (compose_function ht hm)
  let := IsFunction.of_mem he
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function (compose_function ht hm), domain_eq_of_mem_function he]
  · intro p hp
    rw [domain_eq_of_mem_function (compose_function ht hm)] at hp
    rw [value_compose_of_mem_function ht hm hp, woodinStageTag_value hp]
    exact woodinStageMap_fixedPoint_value hδ hAC hγ hfix
      (woodinStageCarrier_fixedPoint_tag_mem hδ hAC hγ hfix hi hp)

end ZFVP
