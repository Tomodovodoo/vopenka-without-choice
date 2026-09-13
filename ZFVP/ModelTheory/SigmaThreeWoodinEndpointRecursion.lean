import ZFVP.ModelTheory.EventualRankCertificateSemantics
import ZFVP.ModelTheory.WoodinSourceEndpointAgreement
import ZFVP.ModelTheory.WoodinRecursionUniform

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def sigmaThreeEndpointRecursionFormula : SetTheorySemisentence 2 :=
  eventualRankCertificate woodinIterationRecFormula

theorem sigmaThreeEndpointRecursionFormula_sigmaThree :
    IsSigmaFormula 3 sigmaThreeEndpointRecursionFormula := eventualRankCertificate_sigmaThree _

theorem eval_sigmaThreeEndpointRecursionFormula {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    letI := hδ.inaccessible.1
    letI := rankDomain_nonempty hδ.inaccessible.2.1
    letI := hδ.inaccessible.rankCriterion.models_zf
    ∀ t : SetDomain (hierarchy δ), IsOrdinal t → ∀ z : SetDomain (hierarchy δ),
      (sigmaThreeEndpointRecursionFormula.Evalb ![z, t] ↔ z = woodinIterationRec t) := by
  let := hδ.inaccessible.1
  let := rankDomain_nonempty hδ.inaccessible.2.1
  let := hδ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive δ
  intro t ht z
  let := (TransitiveZF.ordinal_iff (hierarchy δ) t).mp ht
  have htδ : t.val ∈ δ := ordinal_mem_hierarchy_iff.mp t.property
  obtain ⟨η, hηδ, htη, he⟩ := woodinIterationRec_eventually_rank_eq hδ hAC htδ
  have hh : sigmaThreeEndpointRecursionFormula.Evalb ![z, t] ↔ z.val = woodinIterationRec t.val := by
    apply eval_eventualRankCertificate_of_rank_graph hδ _ z t
    refine ⟨η, hηδ, htη, ?_⟩
    intro ξ hηξ hξ s hs
    let := hξ.1
    let := rankDomain_nonempty hξ.2.1
    let := hξ.rankCriterion.models_zf
    exact ⟨woodinIterationRec s, he ξ hηξ hξ s hs, fun _ ↦ by simp⟩
  rw [← hδ.rank_woodinIterationRec_val hAC t ht] at hh
  exact hh.trans Subtype.ext_iff.symm

end ZFVP
