import ZFVP.ModelTheory.WoodinActualInverseRankAgreement
import ZFVP.ModelTheory.RankNormalizedBaseTwoStep
import ZFVP.ModelTheory.RankNormalizationLimitMaps
import ZFVP.ModelTheory.RankSaturatedHartogsNameAgreement
import ZFVP.ModelTheory.WoodinNormalizationInverse

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_woodinNormalizationInverseMap_val_of_cutoff {Ω : V}
    (hΩ : IsChoicelessInaccessible Ω) :
    letI := hΩ.1
    letI := rankDomain_nonempty hΩ.2.1
    letI := hΩ.rankCriterion.models_zf
    ∀ θ s K m : SetDomain (hierarchy Ω), IsOrdinal θ →
      ∅ ∈ θ.val → IsForcingIterationCode θ.val s.val →
      IsForcingNormalizationFamily θ.val s.val m.val →
      (forcingInverseSourceCutoff θ s (woodinLimitCardinal K)).val =
        forcingInverseSourceCutoff θ.val s.val (woodinLimitCardinal K.val) →
      (woodinNormalizationInverseMap θ s K m).val =
        woodinNormalizationInverseMap θ.val s.val K.val m.val := by
  let := hΩ.1
  let := rankDomain_nonempty hΩ.2.1
  let := hΩ.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro θ s K m hθOrd h0 hcode hn hcut
  let := hθOrd
  let := (TransitiveZF.ordinal_iff (hierarchy Ω) θ).mp hθOrd
  have col := hcode.system.inverseColumn h0 hcode.subset_universe
  have hclosed := hΩ.rankCriterion.2.2.1
  let P := forcingInverseCodePoset θ s
  let R := forcingInverseCodeOrder θ s
  let o := forcingInverseCodeTop θ s
  let γ := woodinLimitCardinal K
  let c := forcingInverseSourceCutoff θ s γ
  let r := forcingNormalizationInverseMap θ s m
  let N := forcingMapFixedPoints P r
  let T := forcingOrderRestriction N R
  let Q := saturatedHartogsPosetName P R o γ c
  have hP : P.val = forcingInverseCodePoset θ.val s.val := rank_forcingInverseCodePoset_val hclosed θ s
  have hR : R.val = forcingInverseCodeOrder θ.val s.val := rank_forcingInverseCodeOrder_val hclosed θ s
  have ho : o.val = forcingInverseCodeTop θ.val s.val := TransitiveZF.forcingInverseCodeTop_val _ θ s
  have hγ : γ.val = woodinLimitCardinal K.val := TransitiveZF.woodinLimitCardinal_val _ K
  have hr : r.val = forcingNormalizationInverseMap θ.val s.val m.val :=
    rank_forcingNormalizationInverseMap_val hclosed θ s m
  have hc : c.val = forcingInverseSourceCutoff θ.val s.val (woodinLimitCardinal K.val) := hcut
  have hpre : IsForcingPreorder P.val R.val := by rw [hP, hR]; exact col.order.preorder
  have htop : IsForcingTop P.val R.val o.val := by rw [hP, hR, ho]; exact col.tops.top
  have hiR := (TransitiveZF.forcingPreorder_iff (hierarchy Ω) P R).mpr hpre
  have hitop := (TransitiveZF.forcingTop_iff (hierarchy Ω) P R o).mpr htop
  have hQ := rank_saturatedHartogsPosetName_val hΩ P R o γ c hiR hitop inferInstance
  change Q.val = saturatedHartogsPosetName P.val R.val o.val γ.val c.val at hQ
  have hN : N.val = forcingMapFixedPoints P.val r.val := TransitiveZF.forcingMapFixedPoints_val _ _ _
  have hT : T.val = forcingOrderRestriction N.val R.val := TransitiveZF.forcingOrderRestriction_val _ _ _
  have hTpre : IsForcingPreorder N.val T.val := by
    rw [hT, hN]
    exact forcingOrderRestriction_preorder hpre sep_subset
  have hone : o.val ∈ N.val := by
    rw [hN, forcingMapFixedPoints, mem_sep_iff]
    refine ⟨htop.1, ?_⟩
    rw [hr, ho]
    simpa only [forcingInverseCode, forcingThreadCode_top, forcingInverseCodeTop] using
      forcingNormalizationInverse_top hcode hn h0
  have he := TransitiveZF.normalizedBaseTwoStepMap_val_rank Ω P R N T o c Q r
    inferInstance hTpre hone
    ((TransitiveZF.forcingName_iff (hierarchy Ω) P Q).mp (saturatedHartogsPosetName_isName P R o γ c))
  simp only [hQ, hT, hN, hP, hR, ho, hγ, hc, hr] at he
  exact he

end ZFVP

