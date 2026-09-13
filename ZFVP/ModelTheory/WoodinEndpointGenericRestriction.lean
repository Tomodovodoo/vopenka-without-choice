import ZFVP.ModelTheory.WoodinEndpointReduction
import ZFVP.ModelTheory.ForcingRegularRestriction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinStageCarrier_endpoint_generic_restrict {δ ε : V} {G : Set V}
    (hδ : IsWoodinSupercompact δ) (hε : IsWoodinSupercompact ε)
    (hAC : ¬InternalChoice V) (hδε : δ ∈ ε)
    (hG : IsExternalForcingGeneric (woodinStageCarrier ε)
      (woodinLocalOrderOn (woodinStageCarrier ε)) G) :
    IsExternalForcingGeneric (woodinStageCarrier δ) (woodinLocalOrderOn (woodinStageCarrier δ))
      {p | p ∈ G ∧ p ∈ woodinStageCarrier δ} := by
  let := hδ.inaccessible.1
  let := hε.inaccessible.1
  have hsub : δ ⊆ ε := IsOrdinal.toIsTransitive.transitive _ hδε
  exact externalForcingGeneric_restrict_of_predense
    (woodinLocalOrderOn_preorder (fun i hi ↦ ((woodinIterationExit hδ hAC).2.1 i hi).1))
    (woodinStageCarrier_endpoint_mono hδ hε hAC hsub)
    (fun _ hp _ hq hpq ↦ (woodinLocalOrderOn_endpoint_agrees hδ hε hAC hsub hp hq).mp hpq)
    (fun _ hp _ hq hc ↦ (woodinStageCarrier_endpoint_compatible_iff hδ hε hAC hδε hp hq).mp hc)
    (fun _ hD hd ↦ (woodinStageCarrier_endpoint_predense hδ hε hAC hδε hD hd).2) hG

end ZFVP
