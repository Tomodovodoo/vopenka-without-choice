import ZFVP.ModelTheory.RankSparseNormalizedTwoStep
import ZFVP.ModelTheory.RankSaturatedPrefixNameAgreement
import ZFVP.ModelTheory.WoodinSparseInitial
import ZFVP.ModelTheory.WoodinInitialStageRankAgreement
import ZFVP.ModelTheory.RankNormalizationMaps

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The actual initial sparse carrier, order and encoding map agree with their
computation at the endpoint rank. All cutoff agreement is derived from the
original restoration computation. -/
theorem rank_woodinInitialSparseAndNormalization_val_of_cutoff {Ω : V}
    (hΩ : IsChoicelessInaccessible Ω) :
    letI := hΩ.1
    letI := rankDomain_nonempty hΩ.2.1
    letI := hΩ.rankCriterion.models_zf
    (woodinSeedCardinal : SetDomain (hierarchy Ω)).val = (woodinSeedCardinal : V) →
    (woodinPrefixCutoff ({∅} : SetDomain (hierarchy Ω)) ({∅} ×ˢ {∅}) ∅ woodinSeedCardinal).val =
      woodinPrefixCutoff ({∅} : V) ({∅} ×ˢ {∅}) ∅ woodinSeedCardinal →
    IsOrdinal (woodinPrefixCutoff ({∅} : SetDomain (hierarchy Ω)) ({∅} ×ˢ {∅}) ∅ woodinSeedCardinal) →
    (woodinSparseInitialCarrier : SetDomain (hierarchy Ω)).val = (woodinSparseInitialCarrier : V) ∧
      (woodinSparseInitialOrder : SetDomain (hierarchy Ω)).val = (woodinSparseInitialOrder : V) ∧
      (woodinSparseInitialMap : SetDomain (hierarchy Ω)).val = (woodinSparseInitialMap : V) ∧
      (woodinNormalizationInitialMap : SetDomain (hierarchy Ω)).val = (woodinNormalizationInitialMap : V) := by
  let := hΩ.1
  let := rankDomain_nonempty hΩ.2.1
  let := hΩ.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro hseed hcut hcOrd
  let P : SetDomain (hierarchy Ω) := {∅}
  let R := P ×ˢ P
  let o : SetDomain (hierarchy Ω) := ∅
  let κ : SetDomain (hierarchy Ω) := woodinSeedCardinal
  let c := woodinPrefixCutoff P R o κ
  let Q := saturatedWoodinPrefixPosetName P R o κ c
  have hP : P.val = ({∅} : V) := by simp only [P, TransitiveZF.singleton_val, TransitiveZF.empty_val]
  have hR : R.val = (({∅} : V) ×ˢ {∅}) := by rw [TransitiveZF.prod_val, hP]
  have ho : o.val = (∅ : V) := TransitiveZF.empty_val _
  have hκ : κ.val = (woodinSeedCardinal : V) := hseed
  have hc : c.val = woodinPrefixCutoff ({∅} : V) (({∅} : V) ×ˢ {∅}) ∅ woodinSeedCardinal := hcut
  have hiR : IsForcingPreorder P R := singletonForcing_preorder ∅
  have hit : IsForcingTop P R o := singletonForcing_top ∅
  have heQ := rank_saturatedWoodinPrefixPosetName_val hΩ P R o κ c hiR hit hcOrd
  change Q.val = saturatedWoodinPrefixPosetName P.val R.val o.val κ.val c.val at heQ
  have heC := TransitiveZF.sparseNormalizedTwoStep_val_rank Ω (succ o) P R o c Q hcOrd
    ((TransitiveZF.forcingPreorder_iff (hierarchy Ω) P R).mp hiR) hit.1
  have heR := TransitiveZF.sparseNormalizedReverseOrder_val_rank Ω (succ o) P R o c Q hcOrd hiR hit
    (saturatedWoodinPrefixPosetName_isName P R o κ c)
  have heW := TransitiveZF.normalizedNamePool_val_rank Ω P R o c Q hcOrd
    ((TransitiveZF.forcingPreorder_iff (hierarchy Ω) P R).mp hiR) hit.1
  have heM := TransitiveZF.sparsePairEncode_val (hierarchy Ω) (succ o) P (normalizedNamePool P R o c Q)
  have heN := TransitiveZF.normalizedTwoStepRetraction_val_rank Ω P R o c Q hcOrd
    ((TransitiveZF.forcingPreorder_iff (hierarchy Ω) P R).mp hiR) hit.1
  rw [heW] at heM
  simp only [TransitiveZF.succ_val, heQ, hP, hR, ho, hκ, hc] at heC heR heM heN
  exact ⟨heC, heR, heM, heN⟩

end ZFVP
