import ZFVP.ModelTheory.WoodinStageRankAgreement
import ZFVP.ModelTheory.RankEnumerationZFC

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Every row of the actual endpoint table has the rank enumeration invariant. -/
theorem woodinIteration_endpoint_rankStage_at {δ i : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V) (hi : i ∈ succ δ) :
    WoodinRankStage i (kpair.π₁ (woodinIterationRec δ)) (kpair.π₂ (woodinIterationRec δ)) := by
  let := hδ.inaccessible.1
  rcases mem_succ_iff.mp hi with rfl | hi
  · exact woodinIteration_endpoint_rankStage hδ hAC
  · have hv := woodinIteration_endpoint_valid hδ hAC
    have hs : ∀ k ∈ δ, IsWoodinIteration (succ δ) (succ k)
        (kpair.π₁ (woodinIterationRec k)) (kpair.π₂ (woodinIterationRec k)) := by
      intro k hk
      exact ((woodinIterationExit hδ hAC).2.1 k hk).1.enlarge_bound
        (fun _ hx ↦ mem_succ_iff.mpr (Or.inr hx))
    exact (woodinIterationRec_rankStage_previous hs hv.1 hi).mp
      (woodinIteration_rankStages hδ i hi)

namespace ForcingContext
variable (A : ForcingContext V) {δ γ : V} (hδ : IsWoodinSupercompact δ)
  (hAC : ¬InternalChoice V) (hγ : γ ∈ succ δ)
  (hfix : (kpair.π₂ (woodinIterationRec δ)) ‘ γ = γ)
  (hP : A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ γ)
  (hR : A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ γ)
  (ht : A.one = (forcingCodet (kpair.π₁ (woodinIterationRec δ))) ‘ γ)

include hδ hAC hγ hfix hP hR ht in
theorem woodinFixedPoint_rankProperties :
    IsRegularCardinal (A.check γ) ∧ HasShortRankEnumerations (A.check γ) (A.check γ) := by
  have hs := ((woodinIteration_endpoint_valid hδ hAC).1.stage γ hγ).2.2.2.1
  have hf : ∀ p ∈ A.P, p ∈ forcingFormula A.P A.R regularCardinalFormula
      (standardTuple ![checkName A.one γ]) := by
    simpa only [woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
      woodinStageTop_code, woodinStageCardinal_code, hfix, hP, hR, ht] using hs
  have hr : ForcesRankEnumerations A.P A.R A.one γ γ := by
    simpa only [WoodinRankStage, hfix, hP, hR, ht] using
      woodinIteration_endpoint_rankStage_at hδ hAC hγ
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  exact ⟨(Defined.eval_iff _).mp ((A.checked_unary_truth regularCardinalFormula γ).mpr
    ⟨p, hp, hf p (A.generic.1.1 p hp)⟩), A.rankEnumerations_of_forced hr⟩

include hδ hAC hγ hfix hP hR ht in
theorem woodinFixedPoint_check_inaccessible : IsChoicelessInaccessible (A.check γ) := by
  obtain ⟨hr, he⟩ := A.woodinFixedPoint_rankProperties hδ hAC hγ hfix hP hR ht
  have hi : IsChoicelessInaccessible γ :=
    hfix ▸ (woodinIteration_endpoint_valid hδ hAC).1.inaccessible γ hγ
  apply he.inaccessible hr
  rw [← A.checkEmbedding.map_omega]
  exact (A.check_mem_iff _ _).mpr hi.2.1

include hδ hAC hγ hfix hP hR ht in
theorem woodinFixedPoint_rank_internalZFModel : IsInternalZFModel (hierarchy (A.check γ)) :=
  (A.woodinFixedPoint_check_inaccessible hδ hAC hγ hfix hP hR ht).internalZFModel

include hδ hAC hγ hfix hP hR ht in
theorem woodinFixedPoint_rank_nonempty : Nonempty (SetDomain (hierarchy (A.check γ))) := by
  have hi := A.woodinFixedPoint_check_inaccessible hδ hAC hγ hfix hP hR ht
  let := hi.1
  exact rankDomain_nonempty hi.2.1

include hδ hAC hγ hfix hP hR ht in
/-- A fixed point of the actual stage-cardinal table has a ZFC rank segment.
Only the outer construction endpoint is assumed supercompact. -/
theorem woodinFixedPoint_rank_models_zfc [Nonempty (SetDomain (hierarchy (A.check γ)))] :
    (SetDomain (hierarchy (A.check γ)))↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 := by
  obtain ⟨hr, he⟩ := A.woodinFixedPoint_rankProperties hδ hAC hγ hfix hP hR ht
  have hi := A.woodinFixedPoint_check_inaccessible hδ hAC hγ hfix hP hR ht
  let := hi.1
  exact rank_models_zfc_of_shortEnumerations he hr hi.2.1

end ForcingContext
end ZFVP
