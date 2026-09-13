import ZFVP.ModelTheory.WoodinLocalRankQuotient
import ZFVP.ModelTheory.WoodinFixedPointRankQuotient
import ZFVP.ModelTheory.DefinableClassGeneric

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace WoodinEndpointModel
variable {δ : V} (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ δ) G)

/-- The actual local endpoint generic meets every dense class definable over
the ground rank, for the externally specified carrier and order. -/
theorem localGeneric_definableClasses : IsGenericForDefinableDenseClasses
    (fun p : SetDomain (hierarchy δ) ↦ p.val ∈ woodinStageCarrier δ)
    (fun p q ↦ ⟨p.val, q.val⟩ₖ ∈ woodinLocalOrderOn (woodinStageCarrier δ))
    {p : SetDomain (hierarchy δ) | p.val ∈ (localContext hδ hAC hG).G} := by
  have h := externalForcingGeneric_definableClasses
    (show (localContext hδ hAC hG).P ⊆ hierarchy δ from woodinIteration_stage_conditions_subset hδ hAC)
    (localContext hδ hAC hG).generic
  rwa [localContext_order hδ hAC hG] at h

/-- Fixed-point local generics also meet all dense classes definable over their
ground ranks. No separate class-generic filter is assumed. -/
theorem fixedPointLocalGeneric_definableClasses {γ : V} (hγ : γ ∈ δ)
    (hfix : (kpair.π₂ (woodinIterationRec δ)) ‘ γ = γ) : IsGenericForDefinableDenseClasses
    (fun p : SetDomain (hierarchy γ) ↦ p.val ∈ woodinStageCarrier γ)
    (fun p q ↦ ⟨p.val, q.val⟩ₖ ∈ woodinLocalOrderOn (woodinStageCarrier γ))
    {p : SetDomain (hierarchy γ) | p.val ∈ (fixedPointLocalContext hδ hAC hG hγ hfix).G} := by
  have h := externalForcingGeneric_definableClasses
    (show (fixedPointLocalContext hδ hAC hG hγ hfix).P ⊆ hierarchy γ from
      woodinStageCarrier_fixedPoint_subset hδ hAC hγ hfix)
    (fixedPointLocalContext hδ hAC hG hγ hfix).generic
  rwa [fixedPointLocalContext_order hδ hAC hG hγ hfix] at h

end WoodinEndpointModel
end ZFVP
