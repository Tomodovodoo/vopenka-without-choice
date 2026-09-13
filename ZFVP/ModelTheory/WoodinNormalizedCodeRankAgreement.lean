import ZFVP.ModelTheory.WoodinNormalizationRecursionRankAgreement
import ZFVP.ModelTheory.TransitiveZFNormalizedRecodedCode
import ZFVP.ModelTheory.WoodinNormalizedCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.rank_woodinNormalizedCode_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ θ : SetDomain (hierarchy Ω), IsOrdinal θ →
      (woodinNormalizedPrefixCode θ).val = woodinNormalizedPrefixCode θ.val ∧
      (woodinNormalizedStageCode θ).val = woodinNormalizedStageCode θ.val := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro θ hθ
  let := hθ
  have hp := TransitiveZF.woodinIterationPrefixes_val_of_previous (hierarchy Ω) θ
    (fun i hi ↦ hΩ.rank_woodinIterationRec_val hAC i (IsOrdinal.of_mem hi))
  constructor
  · unfold woodinNormalizedPrefixCode
    rw [TransitiveZF.forcingNormalizedCode_val, hp.1,
      hΩ.rank_woodinNormalizationHistory_val hAC θ hθ]
  · unfold woodinNormalizedStageCode
    rw [TransitiveZF.forcingNormalizedCode_val, TransitiveZF.kpair_first_val,
      hΩ.rank_woodinIterationRec_val hAC θ hθ,
      hΩ.rank_woodinNormalizationHistory_val hAC (succ θ) inferInstance,
      TransitiveZF.succ_val]
end ZFVP

