import ZFVP.ModelTheory.WoodinEndpointRank
import ZFVP.ModelTheory.RankEnumerationZFC

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext
variable (A : ForcingContext V) {δ : V} (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V)
  (hP : A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
  (hR : A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
  (ht : A.one = (forcingCodet (kpair.π₁ (woodinIterationRec δ))) ‘ δ)

include hδ hAC hP hR ht in
theorem woodinEndpoint_rankProperties :
    IsRegularCardinal (A.check δ) ∧ HasShortRankEnumerations (A.check δ) (A.check δ) := by
  have he := woodinIteration_endpoint_cardinal hδ hAC
  have hs := ((woodinIteration_endpoint_valid hδ hAC).1.stage δ (mem_succ_self δ)).2.2.2.1
  have hf : ∀ p ∈ A.P, p ∈ forcingFormula A.P A.R regularCardinalFormula
      (standardTuple ![checkName A.one δ]) := by
    simpa only [woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
      woodinStageTop_code, woodinStageCardinal_code, he, hP, hR, ht] using hs
  have hr : ForcesRankEnumerations A.P A.R A.one δ δ := by
    simpa only [WoodinRankStage, he, hP, hR, ht] using woodinIteration_endpoint_rankStage hδ hAC
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  exact ⟨(Defined.eval_iff _).mp ((A.checked_unary_truth regularCardinalFormula δ).mpr
    ⟨p, hp, hf p (A.generic.1.1 p hp)⟩), A.rankEnumerations_of_forced hr⟩

include hδ hAC hP hR ht in
theorem woodinEndpoint_check_inaccessible : IsChoicelessInaccessible (A.check δ) := by
  obtain ⟨hr, he⟩ := A.woodinEndpoint_rankProperties hδ hAC hP hR ht
  apply he.inaccessible hr
  rw [← A.checkEmbedding.map_omega]
  exact (A.check_mem_iff _ _).mpr hδ.omega_lt

include hδ hAC hP hR ht in
theorem woodinEndpoint_rank_internalZFModel : IsInternalZFModel (hierarchy (A.check δ)) :=
  (A.woodinEndpoint_check_inaccessible hδ hAC hP hR ht).internalZFModel

include hδ hAC hP hR ht in
theorem woodinEndpoint_rank_nonempty : Nonempty (SetDomain (hierarchy (A.check δ))) := by
  have hi := A.woodinEndpoint_check_inaccessible hδ hAC hP hR ht
  let := hi.1
  exact rankDomain_nonempty hi.2.1

include hδ hAC hP hR ht in
theorem woodinEndpoint_rank_models_zfc [Nonempty (SetDomain (hierarchy (A.check δ)))] :
    (SetDomain (hierarchy (A.check δ)))↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 := by
  obtain ⟨hr, he⟩ := A.woodinEndpoint_rankProperties hδ hAC hP hR ht
  have hi := A.woodinEndpoint_check_inaccessible hδ hAC hP hR ht
  let := hi.1
  exact rank_models_zfc_of_shortEnumerations he hr hi.2.1

end ForcingContext
end ZFVP
