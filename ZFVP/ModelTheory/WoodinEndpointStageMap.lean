import ZFVP.ModelTheory.WoodinEndpointMapCoherence

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinStageMap_endpoint_maps {δ : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V) :
    woodinStageMap δ ∈ ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ) ^
      woodinStageCarrier δ := by
  let := hδ.inaccessible.1
  rw [woodinIteration_endpoint_poset hδ hAC]
  have h := (woodinIterationExit hδ hAC).2.2.1.code
  exact forcingStageThreadMap_maps h.system.split h.subset_universe

theorem woodinStageMap_endpoint_surjective {δ f : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V)
    (hf : f ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ) :
    ∃ z ∈ woodinStageCarrier δ, (woodinStageMap δ) ‘ z = f := by
  let := hδ.inaccessible.1
  rw [woodinIteration_endpoint_poset hδ hAC] at hf
  have h := (woodinIterationExit hδ hAC).2.2.1.code
  exact forcingStageThreadMap_surjective h.system.split h.subset_universe hf

theorem woodinLocalOrderOn_endpoint_pullback {δ : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V) :
    woodinLocalOrderOn (woodinStageCarrier δ) = forcingPullbackOrder (woodinStageCarrier δ)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ δ) (woodinStageMap δ) := by
  let := hδ.inaccessible.1
  rw [woodinIteration_endpoint_order hδ hAC]
  exact woodinLocalOrderOn_eq_pullback (fun i hi ↦ ((woodinIterationExit hδ hAC).2.1 i hi).1)

theorem woodinStageMap_endpoint_compatible_iff {δ z w : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V)
    (hz : z ∈ woodinStageCarrier δ) (hw : w ∈ woodinStageCarrier δ) :
    ForcingCompatible (woodinStageCarrier δ) (woodinLocalOrderOn (woodinStageCarrier δ)) z w ↔
      ForcingCompatible ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
        ((woodinStageMap δ) ‘ z) ((woodinStageMap δ) ‘ w) := by
  rw [woodinLocalOrderOn_endpoint_pullback hδ hAC]
  exact forcingPullbackOrder_compatible_iff (woodinStageMap_endpoint_maps hδ hAC)
    (fun _ hf ↦ woodinStageMap_endpoint_surjective hδ hAC hf) hz hw

end ZFVP
