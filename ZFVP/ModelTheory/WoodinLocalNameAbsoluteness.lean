import ZFVP.ModelTheory.ClassCarrierNameFormula
import ZFVP.ModelTheory.WoodinEndpointLocalAbsoluteness

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Local name syntax for the actual stage-pair presentation. -/
def woodinLocalStageNameFormula : SetTheorySemisentence 1 :=
  classCarrierNameFormula woodinLocalStageConditionFormula

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Neither the endpoint carrier nor a complete endpoint code is an internal
parameter of the name predicate. -/
theorem eval_woodinLocalStageNameFormula_endpoint {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    letI := hδ.inaccessible.1
    letI := rankDomain_nonempty hδ.inaccessible.2.1
    letI := hδ.inaccessible.rankCriterion.models_zf
    ∀ τ : SetDomain (hierarchy δ), woodinLocalStageNameFormula.Evalb ![τ] ↔
      IsForcingName (woodinStageCarrier δ) τ.val := by
  let := hδ.inaccessible.1
  let := rankDomain_nonempty hδ.inaccessible.2.1
  let := hδ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive δ
  exact eval_classCarrierNameFormula_transitive (hierarchy δ)
    woodinLocalStageConditionFormula (woodinStageCarrier δ)
    (eval_woodinLocalStageConditionFormula_endpoint hδ hAC)

end ZFVP
