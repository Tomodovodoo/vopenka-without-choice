import ZFVP.ModelTheory.WoodinNormalizedPrefix
import ZFVP.ModelTheory.WoodinEndpointMapCoherence

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinEndpoint_branch {Ω : V} (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    Ω ≠ ∅ ∧ Ω ≠ succ (⋃ˢ Ω) ∧
      IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix Ω)) := by
  let := hΩ.inaccessible.1
  have hlim : ∀ i ∈ Ω, succ i ∈ Ω := fun _ hi ↦ regularCardinal_succ_closed hΩ.inaccessible.regular hi
  have he := (woodinIterationExit hΩ hAC).2.2.1.limitCardinal_eq_endpoint hlim
  refine ⟨?_, ?_, he.symm ▸ hΩ.inaccessible⟩
  · intro he
    exact not_mem_empty (he ▸ hΩ.inaccessible.2.1)
  · intro he
    have hm : ⋃ˢ Ω ∈ Ω := (congrArg (fun x : V ↦ (⋃ˢ Ω) ∈ x) he).mpr (mem_succ_self _)
    have hn := hlim _ hm
    rw [← he] at hn
    exact mem_irrefl _ hn

theorem woodinNormalizationHistory_endpoint_family {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    IsForcingNormalizationFamily (succ Ω) (kpair.π₁ (woodinIterationRec Ω))
      (woodinNormalizationHistory (succ Ω)) := by
  let := hΩ.inaccessible.1
  obtain ⟨h0, hlim, hi⟩ := woodinEndpoint_branch hΩ hAC
  have hz : (∅ : V) ∈ Ω := (IsOrdinal.subset_iff.mp (empty_subset Ω)).resolve_left (fun he ↦ h0 he.symm)
  have hs := (woodinIterationExit hΩ hAC).2.2.1
  have hn := woodinNormalizationHistory_actual_prefix hΩ hAC (show Ω ⊆ Ω from subset_refl Ω)
  rw [woodinIterationRec_direct h0 hlim hi, kpair.π₁_kpair, woodinNormalizationHistory_next,
    woodinNormalizationRec_rule]
  simpa only [woodinNormalizationRule, ite_eq_right h0, ite_eq_right hlim, ite_eq_left hi,
    forcingNormalizationDirect] using forcingNormalizationDirect_family hs.code hn hz

theorem woodinNormalizationHistory_endpoint_liftClosed {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    IsForcingNormalizationLiftClosed (succ Ω) (kpair.π₁ (woodinIterationRec Ω))
      (woodinNormalizationHistory (succ Ω)) := by
  let := hΩ.inaccessible.1
  obtain ⟨h0, hlim, hi⟩ := woodinEndpoint_branch hΩ hAC
  have hz : (∅ : V) ∈ Ω := (IsOrdinal.subset_iff.mp (empty_subset Ω)).resolve_left (fun he ↦ h0 he.symm)
  have hs := (woodinIterationExit hΩ hAC).2.2.1
  have hn := woodinNormalizationHistory_actual_prefix hΩ hAC (show Ω ⊆ Ω from subset_refl Ω)
  have hL := woodinNormalizationHistory_actual_prefix_liftClosed hΩ hAC (show Ω ⊆ Ω from subset_refl Ω)
  rw [woodinIterationRec_direct h0 hlim hi, kpair.π₁_kpair, woodinNormalizationHistory_next,
    woodinNormalizationRec_rule]
  simpa only [woodinNormalizationRule, ite_eq_right h0, ite_eq_right hlim, ite_eq_left hi,
    forcingNormalizationDirect] using forcingNormalizationDirect_liftClosed hs.code hn hL hz

theorem woodinNormalizedStageCode_endpoint_valid {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    IsForcingIterationCode (succ Ω) (woodinNormalizedStageCode Ω) := by
  let := hΩ.inaccessible.1
  exact (woodinNormalizationHistory_endpoint_liftClosed hΩ hAC).code
    (woodinNormalizationHistory_endpoint_family hΩ hAC) (woodinIteration_endpoint_valid hΩ hAC).1.code

theorem woodinNormalizedStageCode_endpoint_extends {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    ForcingCodeExtends (woodinNormalizedPrefixCode Ω) (woodinNormalizedStageCode Ω) := by
  let := hΩ.inaccessible.1
  apply forcingNormalized_extends (woodinIterationExit hΩ hAC).2.2.1.code
    (woodinIteration_endpoint_valid hΩ hAC).1.code (woodinIterationPrefix_extends_endpoint hΩ hAC)
    (fun _ hi ↦ mem_succ_iff.mpr (Or.inr hi))
    (fun i hi ↦ ?_) (woodinNormalizedPrefixCode_valid hΩ hAC (subset_refl Ω))
    (woodinNormalizedStageCode_endpoint_valid hΩ hAC)
  rw [woodinNormalizationHistory_value hi, woodinNormalizationHistory_value (mem_succ_iff.mpr (Or.inr hi))]

end ZFVP
