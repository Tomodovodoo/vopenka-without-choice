import ZFVP.ModelTheory.WoodinEndpointCompatibility

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Each larger-stage condition has a smaller-stage representative of its projection,
with exactly the same compatibility tests against smaller-stage conditions. -/
theorem woodinStageCarrier_endpoint_reduction {δ ε q : V}
    (hδ : IsWoodinSupercompact δ) (hε : IsWoodinSupercompact ε)
    (hAC : ¬InternalChoice V) (hδε : δ ∈ ε) (hq : q ∈ woodinStageCarrier ε) :
    ∃ z ∈ woodinStageCarrier δ, ∀ w ∈ woodinStageCarrier δ,
      (ForcingCompatible (woodinStageCarrier ε) (woodinLocalOrderOn (woodinStageCarrier ε)) q w ↔
        ForcingCompatible (woodinStageCarrier δ) (woodinLocalOrderOn (woodinStageCarrier δ)) z w) := by
  let := hε.inaccessible.1
  have hsub : δ ⊆ ε := IsOrdinal.toIsTransitive.transitive _ hδε
  have h := woodinIteration_endpoints_splitProjection hδ hε hAC hδε
  have hqP := function_value_mem (woodinStageMap_endpoint_maps hε hAC) hq
  obtain ⟨z, hz, he⟩ := woodinStageMap_endpoint_surjective hδ hAC
    (function_value_mem h.projection.maps hqP)
  refine ⟨z, hz, fun w hw ↦ ?_⟩
  have hwε := woodinStageCarrier_endpoint_mono hδ hε hAC hsub w hw
  rw [woodinStageMap_endpoint_compatible_iff hε hAC hq hwε,
    woodinStageMap_endpoint_compatible_iff hδ hAC hz hw,
    woodinStageMap_endpoint_commutes hδ hε hAC hδε hw, he]
  exact h.compatible_section_iff hqP (function_value_mem (woodinStageMap_endpoint_maps hδ hAC) hw)

/-- Predense sets in the smaller endpoint remain predense after literal inclusion. -/
theorem woodinStageCarrier_endpoint_predense {δ ε D : V}
    (hδ : IsWoodinSupercompact δ) (hε : IsWoodinSupercompact ε)
    (hAC : ¬InternalChoice V) (hδε : δ ∈ ε)
    (hD : D ⊆ woodinStageCarrier δ)
    (hd : ∀ z ∈ woodinStageCarrier δ, ∃ w ∈ D,
      ForcingCompatible (woodinStageCarrier δ) (woodinLocalOrderOn (woodinStageCarrier δ)) z w) :
    D ⊆ woodinStageCarrier ε ∧ ∀ q ∈ woodinStageCarrier ε, ∃ w ∈ D,
      ForcingCompatible (woodinStageCarrier ε) (woodinLocalOrderOn (woodinStageCarrier ε)) q w := by
  let := hε.inaccessible.1
  refine ⟨fun w hw ↦ woodinStageCarrier_endpoint_mono hδ hε hAC
    (IsOrdinal.toIsTransitive.transitive _ hδε) w (hD w hw), ?_⟩
  intro q hq
  obtain ⟨z, hz, he⟩ := woodinStageCarrier_endpoint_reduction hδ hε hAC hδε hq
  obtain ⟨w, hw, hzw⟩ := hd z hz
  exact ⟨w, hw, (he w (hD w hw)).mpr hzw⟩

end ZFVP
