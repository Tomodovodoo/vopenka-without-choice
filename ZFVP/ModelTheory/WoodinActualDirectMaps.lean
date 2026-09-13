import ZFVP.ModelTheory.WoodinRecodedDirect
import ZFVP.ModelTheory.ForcingThreadSpliceTransport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ i a b : V} [IsOrdinal θ]
local notation "S" => woodinIterationPrefix θ
local notation "M" => woodinNormalizationHistory θ
local notation "N" => woodinNormalizedPrefixCode θ
local notation "C" => woodinNormalizedStageCode θ

theorem woodinNormalizedStage_direct_lift
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hi : i ∈ θ) (ha : a ∈ (forcingCodeP C) ‘ θ) (hb : b ∈ (forcingCodeP N) ‘ i) :
    ((forcingCodeL C) ‘ ⟨i, θ⟩ₖ) ‘ ⟨a, b⟩ₖ =
      forcingThreadSplice θ (forcingCodeπ N) (forcingCodeL N) a i b := by
  have hs := woodinIterationPrefix_of_stages
    (fun j hj ↦ ((woodinIterationExit hΩ hAC).2.1 j (hθ j hj)).1)
  have hm := woodinNormalizationHistory_actual_prefix hΩ hAC hθ
  have hbN : b ∈ (forcingNormalizationCarriers θ S M) ‘ i := by
    simpa only [woodinNormalizedPrefixCode, forcingNormalizedCode, forcingCodeP_code] using hb
  have hbP := hm.inclusion i hi b hbN
  have haN : a ∈ (forcingNormalizationCarriers (succ θ) (kpair.π₁ (woodinIterationRec θ))
      (woodinNormalizationHistory (succ θ))) ‘ θ := by
    simpa only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodeP_code] using ha
  have hbN' : b ∈ (forcingNormalizationCarriers (succ θ) (kpair.π₁ (woodinIterationRec θ))
      (woodinNormalizationHistory (succ θ))) ‘ i := by
    simpa only [forcingNormalizationCarriers_value hi,
      forcingNormalizationCarriers_value (mem_succ_iff.mpr (Or.inr hi)),
      woodinNormalizationHistory_value hi,
      woodinNormalizationHistory_value (mem_succ_iff.mpr (Or.inr hi)),
      woodinIterationRec_direct h0 hlim hinac, kpair.π₁_kpair,
      forcingDirectCode, forcingThreadCode, forcingIterationCodeNext, forcingCodeP_code,
      forcingFamilyNext_old hi] using hbN
  have haP := ha
  rw [woodinNormalized_direct_poset h0 hlim hinac] at haP
  have haD := (mem_sep_iff.mp haP).1
  simp only [forcingDirectCode, forcingThreadCode_poset] at haD
  have ha' := ha
  rw [(woodinNormalized_direct_dictionary hΩ hAC hθ h0 hlim hinac).1] at ha'
  have hv := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp
    (forcingDirectLimit_subset _ _ _ _ _ _ ha')).2.1
  have hvN : ∀ j ∈ θ, a ‘ j ∈ (forcingNormalizationCarriers θ S M) ‘ j := by
    simpa only [woodinNormalizedPrefixCode, forcingNormalizedCode, forcingCodeP_code] using hv
  simp only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodeL_code]
  rw [forcingNormalizationLifts_apply (mem_succ_iff.mpr (Or.inr hi)) (mem_succ_self θ) haN hbN',
    woodinIterationRec_direct h0 hlim hinac, kpair.π₁_kpair]
  simp only [forcingDirectCode, forcingThreadCode, forcingIterationCodeNext, forcingCodeL_code,
    forcingMatrixNext_column hi, forcingLimitLiftColumn_value hi, forcingLimitLift_value haD hbP]
  simp only [woodinNormalizedPrefixCode, forcingNormalizedCode, forcingCodeπ_code, forcingCodeL_code]
  exact (forcingNormalized_threadSplice hs.code hm hi hbN hvN).symm

end ZFVP
