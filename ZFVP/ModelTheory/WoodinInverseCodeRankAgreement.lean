import ZFVP.ModelTheory.WoodinInverseCutoffRankAgreement
import ZFVP.ModelTheory.RankInverseTwoStepCode
import ZFVP.ModelTheory.RankSaturatedHartogsNameAgreement
import ZFVP.ModelTheory.SaturatedHartogsStageRankAgreement
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_woodinInverseSourceCode_val {ξ : V} [IsOrdinal ξ]
    [Nonempty (SetDomain (hierarchy ξ))] [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hξ : IsChoicelessInaccessible ξ) (θ s K : SetDomain (hierarchy ξ))
    (hR : IsForcingPreorder (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s))
    (ht : IsForcingTop (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s) (forcingInverseCodeTop θ s))
    (hcut : (forcingInverseSourceCutoff θ s (woodinLimitCardinal K)).val =
      forcingInverseSourceCutoff θ.val s.val (woodinLimitCardinal K.val)) :
    (woodinInverseSourceCode θ s K).val = woodinInverseSourceCode θ.val s.val K.val := by
  let := hierarchy_transitive ξ
  have hclosed : ∀ β ∈ ξ, succ β ∈ ξ := fun _ hb ↦ regularCardinal_succ_closed hξ.regular hb
  let P := forcingInverseCodePoset θ s
  let R := forcingInverseCodeOrder θ s
  let o := forcingInverseCodeTop θ s
  let k := woodinLimitCardinal K
  let c := forcingInverseSourceCutoff θ s k
  let Q := saturatedHartogsPosetName P R o k c
  let S := saturatedHartogsOrderName P R o k c
  have hQ : IsForcingName P Q := saturatedHartogsPosetName_isName _ _ _ _ _
  have hS : IsForcingName P S := reverseInclusionOrderName_isName _ _ _
  have hP : P.val = forcingInverseCodePoset θ.val s.val := rank_forcingInverseCodePoset_val hclosed θ s
  have hRv : R.val = forcingInverseCodeOrder θ.val s.val := rank_forcingInverseCodeOrder_val hclosed θ s
  have ho : o.val = forcingInverseCodeTop θ.val s.val := TransitiveZF.forcingInverseCodeTop_val (hierarchy ξ) θ s
  have hk : k.val = woodinLimitCardinal K.val := TransitiveZF.woodinLimitCardinal_val (hierarchy ξ) K
  have hc : c.val = forcingInverseSourceCutoff θ.val s.val (woodinLimitCardinal K.val) := hcut
  have hQval := rank_saturatedHartogsPosetName_val hξ P R o k c hR ht inferInstance
  have hstage := rank_saturatedHartogsStageAt_val hξ P R o k c hR ht inferInstance
  have horder := congrArg (woodinStageOrder (V := V)) hstage
  rw [← TransitiveZF.woodinStageOrder_val (hierarchy ξ)] at horder
  simp only [saturatedHartogsStageAt, woodinStageOrder_code] at horder
  change (twoStepOrder P R Q S ∅).val = _ at horder
  rw [TransitiveZF.twoStepOrder_val_of_names (hierarchy ξ) P R Q S ∅ hR hQ hS (empty_forcingName P),
    TransitiveZF.empty_val] at horder
  change Q.val = _ at hQval
  rw [hP, hRv, ho, hk, hc] at hQval
  rw [hP, hRv, ho, hk, hc, hQval] at horder
  have hcode := rank_forcingInverseTwoStepCode_val hclosed θ s Q S ∅ hR hQ hS (empty_forcingName P)
  change (woodinInverseSourceCode θ s K).val =
    forcingInverseTwoStepCode θ.val s.val Q.val S.val (∅ : SetDomain (hierarchy ξ)).val at hcode
  rw [TransitiveZF.empty_val, hQval] at hcode
  rw [hcode]
  apply forcingInverseTwoStepCode_order_congr
  exact horder
theorem IsWoodinIteration.eventually_rank_inverseSourceCode_eq {δ θ s K : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hδ : IsWoodinSupercompact δ) (hθ : θ ∈ δ) (h0 : ∅ ∈ θ)
    (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hγ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        (regularCardinalFormula.or limitOfRegularCardinalsFormula)
        (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)]))
    (hDC : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        dependentChoiceAtFormula (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)])) :
    ∃ η ∈ δ, woodinLimitCardinal K ∈ η ∧ ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      ∀ t u C : SetDomain (hierarchy ξ), t.val = θ → u.val = s → C.val = K →
        (woodinInverseSourceCode t u C).val = woodinInverseSourceCode θ s K ∧
          (woodinInverseCardinalNext t u C).val = woodinInverseCardinalNext θ s K := by
  obtain ⟨η, hηδ, hκη, hall⟩ := h.eventually_rank_inverseSourceCutoff_eq hδ hθ h0 hlim hγ hDC
  refine ⟨η, hηδ, hκη, ?_⟩
  intro ξ hηξ hξ
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := hierarchy_transitive ξ
  intro t u C htθ hus hCK
  have hclosed : ∀ β ∈ ξ, succ β ∈ ξ := fun _ hb ↦ regularCardinal_succ_closed hξ.regular hb
  have hP : (forcingInverseCodePoset t u).val = forcingInverseCodePoset θ s := by
    rw [rank_forcingInverseCodePoset_val hclosed, htθ, hus]
  have hR : (forcingInverseCodeOrder t u).val = forcingInverseCodeOrder θ s := by
    rw [rank_forcingInverseCodeOrder_val hclosed, htθ, hus]
  have ho : (forcingInverseCodeTop t u).val = forcingInverseCodeTop θ s := by
    rw [TransitiveZF.forcingInverseCodeTop_val, htθ, hus]
  have hk : (woodinLimitCardinal C).val = woodinLimitCardinal K := by
    rw [TransitiveZF.woodinLimitCardinal_val, hCK]
  have hc := hall ξ hηξ hξ t u C htθ hus hCK
  have col := h.code.system.inverseColumn h0 h.code.subset_universe
  have hpre : IsForcingPreorder (forcingInverseCodePoset t u) (forcingInverseCodeOrder t u) := by
    apply (TransitiveZF.forcingPreorder_iff (hierarchy ξ) _ _).mpr
    rw [hP, hR]
    exact col.order.preorder
  have htop : IsForcingTop (forcingInverseCodePoset t u) (forcingInverseCodeOrder t u)
      (forcingInverseCodeTop t u) := by
    apply (TransitiveZF.forcingTop_iff (hierarchy ξ) _ _ _).mpr
    rw [hP, hR, ho]
    exact col.tops.top
  have hc' : (forcingInverseSourceCutoff t u (woodinLimitCardinal C)).val =
      forcingInverseSourceCutoff t.val u.val (woodinLimitCardinal C.val) := by
    simpa only [htθ, hus, hCK] using hc
  constructor
  · simpa only [htθ, hus, hCK] using rank_woodinInverseSourceCode_val hξ t u C hpre htop hc'
  · simpa only [htθ, hus, hCK] using TransitiveZF.woodinInverseCardinalNext_val (hierarchy ξ) t u C hc'

end ZFVP
