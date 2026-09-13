import ZFVP.ModelTheory.EventualRankCertificateSemantics
import ZFVP.ModelTheory.WoodinSourceEndpointAgreement
import ZFVP.ModelTheory.SigmaThreeWoodinSourcePresentation
import ZFVP.ModelTheory.WoodinRecursionUniform

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def sigmaThreeEndpointSourcePrefixFormula : SetTheorySemisentence 2 :=
  eventualRankCertificate (woodinSourcePrefixCodeCertificate woodinIterationPrefixFormula)

def sigmaThreeEndpointSourceCardinalsFormula : SetTheorySemisentence 2 :=
  eventualRankCertificate (woodinSourcePrefixCardinalsCertificate woodinIterationCardinalPrefixFormula)

def sigmaThreeEndpointSourceCompletedFormula : SetTheorySemisentence 2 :=
  eventualRankCertificate (woodinSourceCompletedCodeCertificate woodinIterationRecFormula)

def sigmaThreeEndpointSourceCompletedCardinalsFormula : SetTheorySemisentence 2 :=
  eventualRankCertificate (woodinSourceCompletedCardinalsCertificate woodinIterationRecFormula)

theorem sigmaThreeEndpointSourcePrefixFormula_sigmaThree :
    IsSigmaFormula 3 sigmaThreeEndpointSourcePrefixFormula := eventualRankCertificate_sigmaThree _

theorem sigmaThreeEndpointSourceCardinalsFormula_sigmaThree :
    IsSigmaFormula 3 sigmaThreeEndpointSourceCardinalsFormula := eventualRankCertificate_sigmaThree _

theorem sigmaThreeEndpointSourceCompletedFormula_sigmaThree :
    IsSigmaFormula 3 sigmaThreeEndpointSourceCompletedFormula := eventualRankCertificate_sigmaThree _

theorem sigmaThreeEndpointSourceCompletedCardinalsFormula_sigmaThree :
    IsSigmaFormula 3 sigmaThreeEndpointSourceCompletedCardinalsFormula := eventualRankCertificate_sigmaThree _

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- All four source-table certificates are evaluated inside the endpoint rank.
Their values are the ambient construction's actual tables. -/
theorem eval_endpointSourcePresentation {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    letI := hδ.inaccessible.1
    letI := rankDomain_nonempty hδ.inaccessible.2.1
    letI := hδ.inaccessible.rankCriterion.models_zf
    ∀ t : SetDomain (hierarchy δ), IsOrdinal t → ∀ z : SetDomain (hierarchy δ),
      (sigmaThreeEndpointSourcePrefixFormula.Evalb ![z, t] ↔
        z.val = woodinSourceCode t.val (woodinIterationPrefix t.val)) ∧
      (sigmaThreeEndpointSourceCardinalsFormula.Evalb ![z, t] ↔
        z.val = woodinSourceCardinals t.val (woodinIterationCardinalPrefix t.val)) ∧
      (sigmaThreeEndpointSourceCompletedFormula.Evalb ![z, t] ↔
        z.val = woodinSourceCode (succ t.val) (kpair.π₁ (woodinIterationRec t.val))) ∧
      (sigmaThreeEndpointSourceCompletedCardinalsFormula.Evalb ![z, t] ↔
        z.val = woodinSourceCardinals (succ t.val) (kpair.π₂ (woodinIterationRec t.val))) := by
  let := hδ.inaccessible.1
  let := rankDomain_nonempty hδ.inaccessible.2.1
  let := hδ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive δ
  intro t ht z
  let := (TransitiveZF.ordinal_iff (hierarchy δ) t).mp ht
  have htδ : t.val ∈ δ := ordinal_mem_hierarchy_iff.mp t.property
  obtain ⟨η, hηδ, htη, he⟩ := woodinSourcePresentation_eventually_rank_eq hδ hAC htδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply eval_eventualRankCertificate_of_rank_graph hδ _ z t
    refine ⟨η, hηδ, htη, ?_⟩
    intro ξ hηξ hξ s hs
    let := hξ.1
    let := rankDomain_nonempty hξ.2.1
    let := hξ.rankCriterion.models_zf
    let := hierarchy_transitive ξ
    have ho : IsOrdinal s := (TransitiveZF.ordinal_iff (hierarchy ξ) s).mpr (hs ▸ inferInstance)
    let := ho
    refine ⟨woodinSourceCode s (woodinIterationPrefix s), (he ξ hηξ hξ s hs).1, ?_⟩
    intro w
    exact eval_woodinSourcePrefixCodeCertificate woodinIterationPrefixFormula w s (fun _ ↦ by simp)
  · apply eval_eventualRankCertificate_of_rank_graph hδ _ z t
    refine ⟨η, hηδ, htη, ?_⟩
    intro ξ hηξ hξ s hs
    let := hξ.1
    let := rankDomain_nonempty hξ.2.1
    let := hξ.rankCriterion.models_zf
    let := hierarchy_transitive ξ
    have ho : IsOrdinal s := (TransitiveZF.ordinal_iff (hierarchy ξ) s).mpr (hs ▸ inferInstance)
    let := ho
    refine ⟨woodinSourceCardinals s (woodinIterationCardinalPrefix s), (he ξ hηξ hξ s hs).2.1, ?_⟩
    intro w
    exact eval_woodinSourcePrefixCardinalsCertificate woodinIterationCardinalPrefixFormula w s (fun _ ↦ by simp)
  · apply eval_eventualRankCertificate_of_rank_graph hδ _ z t
    refine ⟨η, hηδ, htη, ?_⟩
    intro ξ hηξ hξ s hs
    let := hξ.1
    let := rankDomain_nonempty hξ.2.1
    let := hξ.rankCriterion.models_zf
    let := hierarchy_transitive ξ
    have ho : IsOrdinal s := (TransitiveZF.ordinal_iff (hierarchy ξ) s).mpr (hs ▸ inferInstance)
    let := ho
    refine ⟨woodinSourceCode (succ s) (kpair.π₁ (woodinIterationRec s)),
      (he ξ hηξ hξ s hs).2.2.1, ?_⟩
    intro w
    exact eval_woodinSourceCompletedCodeCertificate woodinIterationRecFormula w s (fun _ ↦ by simp)
  · apply eval_eventualRankCertificate_of_rank_graph hδ _ z t
    refine ⟨η, hηδ, htη, ?_⟩
    intro ξ hηξ hξ s hs
    let := hξ.1
    let := rankDomain_nonempty hξ.2.1
    let := hξ.rankCriterion.models_zf
    let := hierarchy_transitive ξ
    have ho : IsOrdinal s := (TransitiveZF.ordinal_iff (hierarchy ξ) s).mpr (hs ▸ inferInstance)
    let := ho
    refine ⟨woodinSourceCardinals (succ s) (kpair.π₂ (woodinIterationRec s)),
      (he ξ hηξ hξ s hs).2.2.2, ?_⟩
    intro w
    exact eval_woodinSourceCompletedCardinalsCertificate woodinIterationRecFormula w s (fun _ ↦ by simp)

/-- Fixed formulas define the actual source prefix and completed-stage tables
inside every Woodin-supercompact endpoint rank in the choiceless construction. -/
theorem woodinEndpointSourcePresentation_sigmaThree_uniform :
    ∃ σ σK σC σL : SetTheorySemisentence 2,
      IsSigmaFormula 3 σ ∧ IsSigmaFormula 3 σK ∧ IsSigmaFormula 3 σC ∧ IsSigmaFormula 3 σL ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙], ∀ δ : V,
        ∀ hδ : IsWoodinSupercompact δ, ¬InternalChoice V →
        letI := hδ.inaccessible.1
        letI := rankDomain_nonempty hδ.inaccessible.2.1
        letI := hδ.inaccessible.rankCriterion.models_zf
        ∀ t : SetDomain (hierarchy δ), IsOrdinal t → ∀ z : SetDomain (hierarchy δ),
          (σ.Evalb ![z, t] ↔ z.val = woodinSourceCode t.val (woodinIterationPrefix t.val)) ∧
          (σK.Evalb ![z, t] ↔ z.val = woodinSourceCardinals t.val (woodinIterationCardinalPrefix t.val)) ∧
          (σC.Evalb ![z, t] ↔ z.val = woodinSourceCode (succ t.val) (kpair.π₁ (woodinIterationRec t.val))) ∧
          (σL.Evalb ![z, t] ↔ z.val = woodinSourceCardinals (succ t.val) (kpair.π₂ (woodinIterationRec t.val))) :=
  ⟨sigmaThreeEndpointSourcePrefixFormula, sigmaThreeEndpointSourceCardinalsFormula,
    sigmaThreeEndpointSourceCompletedFormula, sigmaThreeEndpointSourceCompletedCardinalsFormula,
    sigmaThreeEndpointSourcePrefixFormula_sigmaThree, sigmaThreeEndpointSourceCardinalsFormula_sigmaThree,
    sigmaThreeEndpointSourceCompletedFormula_sigmaThree, sigmaThreeEndpointSourceCompletedCardinalsFormula_sigmaThree,
    fun _ _ _ _ _ hδ hAC ↦ eval_endpointSourcePresentation hδ hAC⟩

end ZFVP
