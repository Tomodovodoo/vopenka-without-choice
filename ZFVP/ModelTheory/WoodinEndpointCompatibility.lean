import ZFVP.ModelTheory.WoodinEndpointStageMap
import ZFVP.ModelTheory.SplitSeparativeOrder
import ZFVP.ModelTheory.IterationSystemProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinIteration_endpoints_splitProjection {δ ε : V}
    (hδ : IsWoodinSupercompact δ) (hε : IsWoodinSupercompact ε)
    (hAC : ¬InternalChoice V) (hδε : δ ∈ ε) :
    IsForcingSplitProjection
      ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
      ((forcingCodeP (kpair.π₁ (woodinIterationRec ε))) ‘ ε)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec ε))) ‘ ε)
      ((forcingCodeπ (kpair.π₁ (woodinIterationRec ε))) ‘ ⟨δ, ε⟩ₖ)
      ((forcingCodeE (kpair.π₁ (woodinIterationRec ε))) ‘ ⟨δ, ε⟩ₖ) := by
  let := hδ.inaccessible.1
  let := hε.inaccessible.1
  have hd := (woodinIteration_endpoint_valid hδ hAC).1.code
  have he := (woodinIteration_endpoint_valid hε hAC).1.code
  have hx := (woodinIterationRec_extends_to_prefix hδε).trans
    (woodinIterationPrefix_extends_endpoint hε hAC)
  rw [hd.tableP.value_of_subset he.tableP hx.subP (mem_succ_self δ),
    hd.tableR.value_of_subset he.tableR hx.subR (mem_succ_self δ)]
  exact he.system.splitProjection (mem_succ_iff.mpr (Or.inr hδε)) (mem_succ_self ε)
    (IsOrdinal.toIsTransitive.transitive _ hδε)

/-- The literal inclusion of endpoint stage codes reflects compatibility. -/
theorem woodinStageCarrier_endpoint_compatible_iff {δ ε z w : V}
    (hδ : IsWoodinSupercompact δ) (hε : IsWoodinSupercompact ε)
    (hAC : ¬InternalChoice V) (hδε : δ ∈ ε)
    (hz : z ∈ woodinStageCarrier δ) (hw : w ∈ woodinStageCarrier δ) :
    ForcingCompatible (woodinStageCarrier ε) (woodinLocalOrderOn (woodinStageCarrier ε)) z w ↔
      ForcingCompatible (woodinStageCarrier δ) (woodinLocalOrderOn (woodinStageCarrier δ)) z w := by
  let := hε.inaccessible.1
  have hsub : δ ⊆ ε := IsOrdinal.toIsTransitive.transitive _ hδε
  have hzε := woodinStageCarrier_endpoint_mono hδ hε hAC hsub z hz
  have hwε := woodinStageCarrier_endpoint_mono hδ hε hAC hsub w hw
  rw [woodinStageMap_endpoint_compatible_iff hε hAC hzε hwε,
    woodinStageMap_endpoint_compatible_iff hδ hAC hz hw,
    woodinStageMap_endpoint_commutes hδ hε hAC hδε hz,
    woodinStageMap_endpoint_commutes hδ hε hAC hδε hw]
  have h := woodinIteration_endpoints_splitProjection hδ hε hAC hδε
  have hzP := function_value_mem (woodinStageMap_endpoint_maps hδ hAC) hz
  have hwP := function_value_mem (woodinStageMap_endpoint_maps hδ hAC) hw
  rw [h.compatible_section_iff (function_value_mem h.maps hzP) hwP, h.right_inverse _ hzP]

end ZFVP
