import ZFVP.ModelTheory.WoodinSparseSuccessorRankAgreement
import ZFVP.ModelTheory.RankNormalizedBaseTwoStep
import ZFVP.ModelTheory.WoodinNormalizationSuccessor

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_woodinNormalizationSuccessorMap_val_of_cutoff {Ω : V}
    (hΩ : IsChoicelessInaccessible Ω) :
    letI := hΩ.1
    letI := rankDomain_nonempty hΩ.2.1
    letI := hΩ.rankCriterion.models_zf
    ∀ k s K m : SetDomain (hierarchy Ω),
      IsWoodinStage (woodinIterationStage s.val K.val k.val) →
      IsForcingNormalizationFamily (succ k.val) s.val m.val →
      (woodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k)
        ((forcingCodet s) ‘ k) (K ‘ k)).val =
        woodinPrefixCutoff ((forcingCodeP s.val) ‘ k.val) ((forcingCodeR s.val) ‘ k.val)
          ((forcingCodet s.val) ‘ k.val) (K.val ‘ k.val) →
      IsOrdinal (woodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k)
        ((forcingCodet s) ‘ k) (K ‘ k)) →
      (woodinNormalizationSuccessorMap k s K m).val =
        woodinNormalizationSuccessorMap k.val s.val K.val m.val := by
  let := hΩ.1
  let := rankDomain_nonempty hΩ.2.1
  let := hΩ.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro k s K m hs hn hcut hδOrd
  let P := (forcingCodeP s) ‘ k
  let R := (forcingCodeR s) ‘ k
  let o := (forcingCodet s) ‘ k
  let κ := K ‘ k
  let δ := woodinPrefixCutoff P R o κ
  let Q := saturatedWoodinPrefixPosetName P R o κ δ
  let f := m ‘ k
  let N := forcingMapFixedPoints P f
  let T := forcingOrderRestriction N R
  have hP : P.val = (forcingCodeP s.val) ‘ k.val := by
    rw [TransitiveZF.value_val_total, TransitiveZF.forcingCodeP_val]
  have hR : R.val = (forcingCodeR s.val) ‘ k.val := by
    rw [TransitiveZF.value_val_total, TransitiveZF.forcingCodeR_val]
  have ho : o.val = (forcingCodet s.val) ‘ k.val := by
    rw [TransitiveZF.value_val_total, TransitiveZF.forcingCodet_val]
  have hκ : κ.val = K.val ‘ k.val := TransitiveZF.value_val_total _ _ _
  have hf : f.val = m.val ‘ k.val := TransitiveZF.value_val_total _ _ _
  have hs' : IsWoodinStage (woodinStageCode P.val R.val o.val κ.val) := by
    simpa only [hP, hR, ho, hκ, woodinIterationStage] using hs
  have hδ : δ.val = woodinPrefixCutoff P.val R.val o.val κ.val := by
    simpa only [hP, hR, ho, hκ] using hcut
  simp only [IsWoodinStage, woodinStagePoset_code, woodinStageOrder_code,
    woodinStageTop_code, woodinStageCardinal_code] at hs'
  have hiR := (TransitiveZF.forcingPreorder_iff (hierarchy Ω) P R).mpr hs'.1
  have hit := (TransitiveZF.forcingTop_iff (hierarchy Ω) P R o).mpr hs'.2.1
  have hQ := rank_saturatedWoodinPrefixPosetName_val hΩ P R o κ δ hiR hit hδOrd
  change Q.val = saturatedWoodinPrefixPosetName P.val R.val o.val κ.val δ.val at hQ
  have hN : N.val = forcingMapFixedPoints P.val f.val := TransitiveZF.forcingMapFixedPoints_val _ _ _
  have hT : T.val = forcingOrderRestriction N.val R.val := TransitiveZF.forcingOrderRestriction_val _ _ _
  have hTpre : IsForcingPreorder N.val T.val := by
    rw [hT, hN]
    exact forcingOrderRestriction_preorder hs'.1 sep_subset
  have hone : o.val ∈ N.val := by
    rw [hN, forcingMapFixedPoints, mem_sep_iff]
    refine ⟨hs'.2.1.1, ?_⟩
    rw [hf, ho]
    exact hn.fixesTop k.val (mem_succ_self k.val)
  have he := TransitiveZF.normalizedBaseTwoStepMap_val_rank Ω P R N T o δ Q f hδOrd hTpre hone
    ((TransitiveZF.forcingName_iff (hierarchy Ω) P Q).mp (saturatedWoodinPrefixPosetName_isName P R o κ δ))
  simp only [hQ, hδ, hT, hN, hP, hR, ho, hκ, hf] at he
  exact he

end ZFVP
