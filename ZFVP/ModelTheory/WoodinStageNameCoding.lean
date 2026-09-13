import ZFVP.ModelTheory.WoodinEndpointStageMap
import ZFVP.ModelTheory.ForcingNameActionRank
import ZFVP.SetTheory.InaccessibleFunctionClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinStageTag (δ i : V) : V :=
  definableGraph ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ i)
    (fun p ↦ ⟨i, p⟩ₖ) (by definability)

theorem woodinStageTag_value {δ i p : V}
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ i) :
    (woodinStageTag δ i) ‘ p = ⟨i, p⟩ₖ := value_definableGraph _ _ _ hp

variable {δ i : V} (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (hi : i ∈ δ)
include hδ hAC hi

theorem woodinIteration_endpoint_earlier_poset_small :
    (forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ i ∈ hierarchy δ := by
  let := hδ.inaccessible.1
  have h := (woodinIteration_endpoint_valid hδ hAC).1
  have hi' : i ∈ succ δ := mem_succ_iff.mpr (Or.inr hi)
  have hb := h.increasing i hi' δ (mem_succ_self δ) hi
  rw [woodinIteration_endpoint_cardinal hδ hAC] at hb
  have hs := h.small i hi' δ hδ.inaccessible
  simp only [woodinIterationStage, woodinStagePoset_code, woodinStageCardinal_code] at hs
  exact hs hb

theorem woodinStageCarrier_tag_mem {p : V}
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ i) :
    ⟨i, p⟩ₖ ∈ woodinStageCarrier δ := by
  let := hδ.inaccessible.1
  have h := (woodinIterationExit hδ hAC).2.2.1.code
  have h' := (woodinIteration_endpoint_valid hδ hAC).1.code
  have hp' : p ∈ (forcingCodeP (woodinIterationPrefix δ)) ‘ i := by
    rwa [h.tableP.value_of_subset h'.tableP (woodinIterationPrefix_extends_endpoint hδ hAC).subP hi]
  exact (kpair_mem_forcingStageConditions_iff _ _ _ _ _).mpr
    ⟨hi, h.subset_universe i hi p hp', hp'⟩

theorem woodinStageTag_maps :
    woodinStageTag δ i ∈ (woodinStageCarrier δ) ^
      ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ i) :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hp ↦ woodinStageCarrier_tag_mem hδ hAC hi hp)

theorem woodinStageTag_mem_hierarchy : woodinStageTag δ i ∈ hierarchy δ :=
  hδ.inaccessible.function_mem (woodinIteration_endpoint_earlier_poset_small hδ hAC hi)
    (mem_function_of_mem_function_of_subset (woodinStageTag_maps hδ hAC hi)
      (woodinIteration_stage_conditions_subset hδ hAC))

theorem woodinStageTag_compose_endpoint :
    compose (woodinStageTag δ i) (woodinStageMap δ) =
      (forcingCodeE (kpair.π₁ (woodinIterationRec δ))) ‘ ⟨i, δ⟩ₖ := by
  let := hδ.inaccessible.1
  have ht := woodinStageTag_maps hδ hAC hi
  have hm := woodinStageMap_endpoint_maps hδ hAC
  have he := (woodinIteration_endpoint_valid hδ hAC).1.code.system.functions.sectionMap
    i (mem_succ_iff.mpr (Or.inr hi)) δ (mem_succ_self δ) (IsOrdinal.toIsTransitive.transitive _ hi)
  let := IsFunction.of_mem (compose_function ht hm)
  let := IsFunction.of_mem he
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function (compose_function ht hm), domain_eq_of_mem_function he]
  · intro p hp
    rw [domain_eq_of_mem_function (compose_function ht hm)] at hp
    rw [value_compose_of_mem_function ht hm hp, woodinStageTag_value hp]
    exact woodinStageMap_endpoint_value hδ hAC (woodinStageCarrier_tag_mem hδ hAC hi hp)

theorem woodinStageTag_name_mem_hierarchy {τ : V}
    (hτ : IsForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ i) τ)
    (hτδ : τ ∈ hierarchy δ) : nameAction (woodinStageTag δ i) τ ∈ hierarchy δ :=
  nameAction_mem_hierarchy_of_inaccessible hδ.inaccessible
    (woodinIteration_endpoint_earlier_poset_small hδ hAC hi)
    (woodinStageTag_mem_hierarchy hδ hAC hi) hτδ hτ

end ZFVP
