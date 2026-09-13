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
theorem IsWoodinSupercompact.rank_woodinInitialSparseAndNormalization_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    (woodinSparseInitialCarrier : SetDomain (hierarchy Ω)).val = (woodinSparseInitialCarrier : V) ∧
      (woodinSparseInitialOrder : SetDomain (hierarchy Ω)).val = (woodinSparseInitialOrder : V) ∧
      (woodinSparseInitialMap : SetDomain (hierarchy Ω)).val = (woodinSparseInitialMap : V) ∧
      (woodinNormalizationInitialMap : SetDomain (hierarchy Ω)).val = (woodinNormalizationInitialMap : V) := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  let P : SetDomain (hierarchy Ω) := {∅}
  let R := P ×ˢ P
  let o : SetDomain (hierarchy Ω) := ∅
  let κ : SetDomain (hierarchy Ω) := woodinSeedCardinal
  let c := woodinPrefixCutoff P R o κ
  let Q := saturatedWoodinPrefixPosetName P R o κ c
  have hP : P.val = ({∅} : V) := by simp only [P, TransitiveZF.singleton_val, TransitiveZF.empty_val]
  have hR : R.val = (({∅} : V) ×ˢ {∅}) := by rw [TransitiveZF.prod_val, hP]
  have ho : o.val = (∅ : V) := TransitiveZF.empty_val _
  obtain ⟨η, hη, hseed⟩ := hΩ.eventually_rank_woodinSeedCardinal_eq hAC
  have hκ : κ.val = (woodinSeedCardinal : V) := hseed Ω hη hΩ.inaccessible
  obtain ⟨η', hη', hstage⟩ := hΩ.eventually_rank_woodinInitialStage_eq hAC
  have hc0 := congrArg woodinStageCardinal (hstage Ω hη' hΩ.inaccessible)
  rw [← TransitiveZF.woodinStageCardinal_val] at hc0
  have hc : c.val = woodinPrefixCutoff ({∅} : V) (({∅} : V) ×ˢ {∅}) ∅ woodinSeedCardinal := by
    simpa only [woodinInitialStage, woodinSuccessorStep, woodinSuccessorAt,
      woodinSeedStage, woodinStagePoset_code, woodinStageOrder_code, woodinStageTop_code,
      woodinStageCardinal_code] using hc0
  have hcOrd : IsOrdinal c := (TransitiveZF.ordinal_iff (hierarchy Ω) c).mpr
    (hc ▸ (woodinNormalizationInitial_inputs hΩ).1.1)
  have hiR : IsForcingPreorder P R := singletonForcing_preorder ∅
  have hit : IsForcingTop P R o := singletonForcing_top ∅
  have heQ := rank_saturatedWoodinPrefixPosetName_val hΩ.inaccessible P R o κ c hiR hit hcOrd
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

theorem IsWoodinSupercompact.rank_woodinSparseInitial_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    (woodinSparseInitialCarrier : SetDomain (hierarchy Ω)).val = (woodinSparseInitialCarrier : V) ∧
      (woodinSparseInitialOrder : SetDomain (hierarchy Ω)).val = (woodinSparseInitialOrder : V) ∧
      (woodinSparseInitialMap : SetDomain (hierarchy Ω)).val = (woodinSparseInitialMap : V) := by
  obtain ⟨hP, hR, hm, _⟩ := hΩ.rank_woodinInitialSparseAndNormalization_val hAC
  exact ⟨hP, hR, hm⟩

theorem IsWoodinSupercompact.rank_woodinNormalizationInitialMap_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    (woodinNormalizationInitialMap : SetDomain (hierarchy Ω)).val = (woodinNormalizationInitialMap : V) :=
  (hΩ.rank_woodinInitialSparseAndNormalization_val hAC).2.2.2

end ZFVP
