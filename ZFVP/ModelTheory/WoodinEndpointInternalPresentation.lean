import ZFVP.ModelTheory.SigmaThreeWoodinEndpointOrder
import ZFVP.ModelTheory.WoodinLocalClassGeneric

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

/-- The actual stage-code presentation has uniform internal Sigma-three carrier
and order definitions at every Woodin-supercompact endpoint. -/
theorem woodinEndpointStagePresentation_sigmaThree_uniform :
    ∃ φ : SetTheorySemisentence 1, ∃ ψ : SetTheorySemisentence 2,
      IsSigmaFormula 3 φ ∧ IsSigmaFormula 3 ψ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙], ∀ δ : V,
        ∀ hδ : IsWoodinSupercompact δ, ¬InternalChoice V →
        letI := hδ.inaccessible.1
        letI := rankDomain_nonempty hδ.inaccessible.2.1
        letI := hδ.inaccessible.rankCriterion.models_zf
        (∀ z : SetDomain (hierarchy δ), φ.Evalb ![z] ↔ z.val ∈ woodinStageCarrier δ) ∧
        (∀ z w : SetDomain (hierarchy δ), ψ.Evalb ![z, w] ↔
          ⟨z.val, w.val⟩ₖ ∈ woodinLocalOrderOn (woodinStageCarrier δ)) :=
  ⟨sigmaThreeEndpointStageCarrierFormula, sigmaThreeEndpointStageOrderFormula,
    sigmaThreeEndpointStageCarrierFormula_sigmaThree, sigmaThreeEndpointStageOrderFormula_sigmaThree,
    fun _ _ _ _ _ hδ hAC ↦ ⟨eval_sigmaThreeEndpointStageCarrierFormula hδ hAC,
      eval_sigmaThreeEndpointStageOrderFormula hδ hAC⟩⟩

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinStageMap_endpoint_projection {δ : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V) :
    IsForcingProjection ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
      (woodinStageCarrier δ) (woodinLocalOrderOn (woodinStageCarrier δ)) (woodinStageMap δ) := by
  rw [woodinLocalOrderOn_endpoint_pullback hδ hAC]
  exact forcingPullbackOrder_projection (woodinStageMap_endpoint_maps hδ hAC)
    (fun _ hf ↦ woodinStageMap_endpoint_surjective hδ hAC hf)

namespace WoodinEndpointModel

/-- The pulled-back endpoint generic is generic for the internally defined
Sigma-three forcing, against all rank-definable dense classes with parameters. -/
theorem localGeneric_internalSigmaThree {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) {G : Set V}
    (hG : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ δ) G) :
    letI := hδ.inaccessible.1
    letI := rankDomain_nonempty hδ.inaccessible.2.1
    letI := hδ.inaccessible.rankCriterion.models_zf
    IsGenericForDefinableDenseClasses
      (fun p : SetDomain (hierarchy δ) ↦ sigmaThreeEndpointStageCarrierFormula.Evalb ![p])
      (fun p q : SetDomain (hierarchy δ) ↦ sigmaThreeEndpointStageOrderFormula.Evalb ![p, q])
      {p : SetDomain (hierarchy δ) | p.val ∈ (localContext hδ hAC hG).G} := by
  let := hδ.inaccessible.1
  let := rankDomain_nonempty hδ.inaccessible.2.1
  let := hδ.inaccessible.rankCriterion.models_zf
  have hP : (fun p : SetDomain (hierarchy δ) ↦ sigmaThreeEndpointStageCarrierFormula.Evalb ![p]) =
      (fun p : SetDomain (hierarchy δ) ↦ p.val ∈ woodinStageCarrier δ) :=
    funext fun p ↦ propext (eval_sigmaThreeEndpointStageCarrierFormula hδ hAC p)
  have hR : (fun p q : SetDomain (hierarchy δ) ↦ sigmaThreeEndpointStageOrderFormula.Evalb ![p, q]) =
      (fun p q : SetDomain (hierarchy δ) ↦ ⟨p.val, q.val⟩ₖ ∈ woodinLocalOrderOn (woodinStageCarrier δ)) :=
    funext fun p ↦ funext fun q ↦ propext (eval_sigmaThreeEndpointStageOrderFormula hδ hAC p q)
  rw [hP, hR]
  exact localGeneric_definableClasses hδ hAC hG

end WoodinEndpointModel
end ZFVP
