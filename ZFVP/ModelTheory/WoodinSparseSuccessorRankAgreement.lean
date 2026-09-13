import ZFVP.ModelTheory.RankSparseNormalizedTwoStep
import ZFVP.ModelTheory.RankSaturatedPrefixNameAgreement
import ZFVP.ModelTheory.WoodinSparseSuccessor
import ZFVP.ModelTheory.WoodinSourceEndpointAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- At the outer supercompact, a legitimate completed stage determines the
same least restoration cutoff internally and externally. -/
theorem IsWoodinSupercompact.rank_prefixCutoff_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ P R one κ : SetDomain (hierarchy Ω),
      IsWoodinStage (woodinStageCode P.val R.val one.val κ.val) →
      (woodinPrefixCutoff P R one κ).val = woodinPrefixCutoff P.val R.val one.val κ.val := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  intro P R one κ hs
  simp only [IsWoodinStage, woodinStagePoset_code, woodinStageOrder_code,
    woodinStageTop_code, woodinStageCardinal_code] at hs
  let := hs.2.2.1
  obtain ⟨η, hη, _, hh⟩ := hΩ.eventually_rank_woodinPrefixCutoff_eq hs.1 hs.2.1
    P.property R.property (ordinal_mem_hierarchy_iff.mp κ.property) hs.2.2.2.1 hs.2.2.2.2
  exact hh Ω hη hΩ.inaccessible P R one κ rfl rfl rfl rfl

/-- Comparison of the actual sparse successor constructors on a legitimate
completed input row. The previous code is a parameter; no agreement premise
for the successor pool, carrier, order, or restoration test is assumed. -/
theorem IsWoodinSupercompact.rank_woodinSparseSuccessor_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ k c : SetDomain (hierarchy Ω), IsOrdinal k →
      IsWoodinStage (woodinIterationStage c.val (kpair.π₂ (woodinIterationRec k.val)) k.val) →
      (woodinSparseSuccessorPool k c).val = woodinSparseSuccessorPool k.val c.val ∧
      (woodinSparseSuccessorCarrier k c).val = woodinSparseSuccessorCarrier k.val c.val ∧
      (woodinSparseSuccessorOrder k c).val = woodinSparseSuccessorOrder k.val c.val := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro k c hk hs
  let := hk
  let P := (forcingCodeP c) ‘ k
  let R := (forcingCodeR c) ‘ k
  let o := (forcingCodet c) ‘ k
  let κ := (kpair.π₂ (woodinIterationRec k)) ‘ k
  let δ := woodinPrefixCutoff P R o κ
  let Q := saturatedWoodinPrefixPosetName P R o κ δ
  let a := woodinSourceIndex (succ k)
  have hP : P.val = (forcingCodeP c.val) ‘ k.val := by
    rw [TransitiveZF.value_val_total, TransitiveZF.forcingCodeP_val]
  have hR : R.val = (forcingCodeR c.val) ‘ k.val := by
    rw [TransitiveZF.value_val_total, TransitiveZF.forcingCodeR_val]
  have ho : o.val = (forcingCodet c.val) ‘ k.val := by
    rw [TransitiveZF.value_val_total, TransitiveZF.forcingCodet_val]
  have hκ : κ.val = (kpair.π₂ (woodinIterationRec k.val)) ‘ k.val := by
    rw [TransitiveZF.value_val_total, TransitiveZF.kpair_second_val,
      hΩ.rank_woodinIterationRec_val hAC k hk]
  have hs' : IsWoodinStage (woodinStageCode P.val R.val o.val κ.val) := by
    simpa only [hP, hR, ho, hκ, woodinIterationStage] using hs
  have hδ := hΩ.rank_prefixCutoff_val P R o κ hs'
  change δ.val = woodinPrefixCutoff P.val R.val o.val κ.val at hδ
  simp only [IsWoodinStage, woodinStagePoset_code, woodinStageOrder_code,
    woodinStageTop_code, woodinStageCardinal_code] at hs'
  let := hs'.2.2.1
  obtain ⟨d, _, hd⟩ := hΩ.strictPrefixCutoff hs'.1 hs'.2.1 P.property R.property
    (ordinal_mem_hierarchy_iff.mp κ.property) hs'.2.2.2.1 hs'.2.2.2.2
  have hδOrd : IsOrdinal δ := (TransitiveZF.ordinal_iff (hierarchy Ω) δ).mpr
    (hδ ▸ (woodinPrefixCutoff_spec hd).1)
  have hiR := (TransitiveZF.forcingPreorder_iff (hierarchy Ω) P R).mpr hs'.1
  have hit := (TransitiveZF.forcingTop_iff (hierarchy Ω) P R o).mpr hs'.2.1
  have hQ := rank_saturatedWoodinPrefixPosetName_val hΩ.inaccessible P R o κ δ hiR hit hδOrd
  change Q.val = saturatedWoodinPrefixPosetName P.val R.val o.val κ.val δ.val at hQ
  have ha : a.val = woodinSourceIndex (succ k.val) := by
    rw [TransitiveZF.woodinSourceIndex_val (hierarchy Ω) (succ k) inferInstance, TransitiveZF.succ_val]
  have heW := TransitiveZF.normalizedNamePool_val_rank Ω P R o δ Q hδOrd hs'.1 hs'.2.1.1
  have heC := TransitiveZF.sparseNormalizedTwoStep_val_rank Ω a P R o δ Q hδOrd hs'.1 hs'.2.1.1
  have heR := TransitiveZF.sparseNormalizedReverseOrder_val_rank Ω a P R o δ Q hδOrd hiR hit
    (saturatedWoodinPrefixPosetName_isName P R o κ δ)
  simp only [ha, hQ, hδ, hP, hR, ho, hκ] at heW heC heR
  exact ⟨heW, heC, heR⟩

end ZFVP
