import ZFVP.ModelTheory.WoodinSparseRecursionRankAgreement
import ZFVP.ModelTheory.WoodinSparseStageCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.rank_woodinSparseCode_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ θ : SetDomain (hierarchy Ω), IsOrdinal θ →
      (woodinSparsePrefixCode θ).val = woodinSparsePrefixCode θ.val ∧
      (woodinSparseStageCode θ).val = woodinSparseStageCode θ.val := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro θ hθ
  let := hθ
  have hn := hΩ.rank_woodinNormalizedCode_val hAC θ hθ
  constructor
  · unfold woodinSparsePrefixCode
    rw [TransitiveZF.forcingRecodedCode_val, TransitiveZF.woodinRecodingCarriers_val,
      TransitiveZF.woodinRecodingOrders_val, TransitiveZF.woodinRecodingMaps_val,
      hΩ.rank_woodinSparseRecodingHistory_val hAC θ hθ, hn.1]
  · unfold woodinSparseStageCode
    rw [TransitiveZF.forcingRecodedCode_val, TransitiveZF.woodinRecodingCarriers_val,
      TransitiveZF.woodinRecodingOrders_val, TransitiveZF.woodinRecodingMaps_val,
      hΩ.rank_woodinSparseRecodingHistory_val hAC (succ θ) inferInstance,
      hn.2, TransitiveZF.succ_val]
end ZFVP
