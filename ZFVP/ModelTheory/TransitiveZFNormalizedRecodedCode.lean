import ZFVP.ModelTheory.RankNormalizationMaps
import ZFVP.ModelTheory.ForcingNormalizedCode
import ZFVP.ModelTheory.ForcingRecodedCode
import ZFVP.ModelTheory.WoodinRecodingRecursion
import ZFVP.ModelTheory.TransitiveZFTwoStepColumns
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingMapFixedPoints_val (P m : SetDomain U) :
    (forcingMapFixedPoints P m).val = forcingMapFixedPoints P.val m.val := by
  unfold forcingMapFixedPoints
  apply sep_val U
  intro p _
  rw [← value_val_total U]
  exact ⟨congrArg Subtype.val, Subtype.ext⟩

theorem forcingOrderRestriction_val (N R : SetDomain U) :
    (forcingOrderRestriction N R).val = forcingOrderRestriction N.val R.val := by
  unfold forcingOrderRestriction
  rw [← prod_val U]
  apply sep_val U
  intro z _
  rfl

theorem forcingMapOn_val (A f : SetDomain U) :
    (forcingMapOn A f).val = forcingMapOn A.val f.val := by
  unfold forcingMapOn
  apply definableGraph_val U
  intro p _
  exact value_val_total U f p

theorem forcingNormalizationCarriers_val (θ s m : SetDomain U) :
    (forcingNormalizationCarriers θ s m).val = forcingNormalizationCarriers θ.val s.val m.val := by
  unfold forcingNormalizationCarriers
  apply definableGraph_val U
  intro x _
  simp only [forcingMapFixedPoints_val U, value_val_total U, forcingCodeP_val U]

theorem forcingNormalizationOrders_val (θ s m : SetDomain U) :
    (forcingNormalizationOrders θ s m).val = forcingNormalizationOrders θ.val s.val m.val := by
  unfold forcingNormalizationOrders
  apply definableGraph_val U
  intro x _
  simp only [forcingOrderRestriction_val U, value_val_total U, forcingNormalizationCarriers_val U, forcingCodeR_val U]

theorem forcingNormalizationProjections_val (θ s m : SetDomain U) :
    (forcingNormalizationProjections θ s m).val = forcingNormalizationProjections θ.val s.val m.val := by
  unfold forcingNormalizationProjections
  rw [← prod_val U]
  apply definableGraph_val U
  intro x _
  simp only [restrict_val U, value_val_total U, forcingCodeπ_val U, forcingNormalizationCarriers_val U, kpair_second_val U]

theorem forcingNormalizationSections_val (θ s m : SetDomain U) :
    (forcingNormalizationSections θ s m).val = forcingNormalizationSections θ.val s.val m.val := by
  unfold forcingNormalizationSections
  rw [← prod_val U]
  apply definableGraph_val U
  intro x _
  simp only [restrict_val U, value_val_total U, forcingCodeE_val U, forcingNormalizationCarriers_val U, kpair_first_val U]

theorem forcingNormalizationLifts_val (θ s m : SetDomain U) :
    (forcingNormalizationLifts θ s m).val = forcingNormalizationLifts θ.val s.val m.val := by
  unfold forcingNormalizationLifts
  rw [← prod_val U]
  apply definableGraph_val U
  intro x _
  simp only [forcingMapOn_val U, prod_val U, value_val_total U, forcingNormalizationCarriers_val U, forcingCodeL_val U, kpair_second_val U, kpair_first_val U]

theorem forcingRecodedProjections_val (θ s m : SetDomain U) :
    (forcingRecodedProjections θ s m).val = forcingRecodedProjections θ.val s.val m.val := by
  unfold forcingRecodedProjections
  rw [← prod_val U]
  apply definableGraph_val U
  intro x _
  simp only [compose_val U, converseGraph_val U, value_val_total U, forcingCodeπ_val U, kpair_second_val U, kpair_first_val U]

theorem forcingRecodedSections_val (θ s m : SetDomain U) :
    (forcingRecodedSections θ s m).val = forcingRecodedSections θ.val s.val m.val := by
  unfold forcingRecodedSections
  rw [← prod_val U]
  apply definableGraph_val U
  intro x _
  simp only [compose_val U, converseGraph_val U, value_val_total U, forcingCodeE_val U, kpair_second_val U, kpair_first_val U]

theorem forcingRecodedLiftMap_val (Q L m z : SetDomain U) :
    (forcingRecodedLiftMap Q L m z).val = forcingRecodedLiftMap Q.val L.val m.val z.val := by
  unfold forcingRecodedLiftMap
  have hd : ((Q ‘ (kpair.π₂ z)) ×ˢ (Q ‘ (kpair.π₁ z))).val = (Q.val ‘ (kpair.π₂ z.val)) ×ˢ (Q.val ‘ (kpair.π₁ z.val)) := by
    simp only [prod_val U, value_val_total U, kpair_first_val U, kpair_second_val U]
  rw [← hd]
  apply definableGraph_val U
  intro x _
  simp only [value_val_total U, converseGraph_val U, kpair_val U, kpair_second_val U, kpair_first_val U]

theorem forcingRecodedLifts_val (θ s Q m : SetDomain U) :
    (forcingRecodedLifts θ s Q m).val = forcingRecodedLifts θ.val s.val Q.val m.val := by
  unfold forcingRecodedLifts
  rw [← prod_val U]
  apply definableGraph_val U
  intro x _
  simp only [forcingRecodedLiftMap_val U, forcingCodeL_val U]

theorem forcingRecodedTops_val (θ s m : SetDomain U) :
    (forcingRecodedTops θ s m).val = forcingRecodedTops θ.val s.val m.val := by
  unfold forcingRecodedTops
  apply definableGraph_val U
  intro x _
  simp only [value_val_total U, forcingCodet_val U]

theorem woodinRecodingCarriers_val (H : SetDomain U) :
    (woodinRecodingCarriers H).val = woodinRecodingCarriers H.val := by
  unfold woodinRecodingCarriers
  rw [← domain_val U]
  apply definableGraph_val U
  intro x _
  simp only [kpair_first_val U, value_val_total U]

theorem woodinRecodingOrders_val (H : SetDomain U) :
    (woodinRecodingOrders H).val = woodinRecodingOrders H.val := by
  unfold woodinRecodingOrders
  rw [← domain_val U]
  apply definableGraph_val U
  intro x _
  simp only [kpair_first_val U, kpair_second_val U, value_val_total U]

theorem woodinRecodingMaps_val (H : SetDomain U) :
    (woodinRecodingMaps H).val = woodinRecodingMaps H.val := by
  unfold woodinRecodingMaps
  rw [← domain_val U]
  apply definableGraph_val U
  intro x _
  simp only [kpair_second_val U, value_val_total U]

theorem forcingNormalizedCode_val (θ s m : SetDomain U) :
    (forcingNormalizedCode θ s m).val = forcingNormalizedCode θ.val s.val m.val := by
  unfold forcingNormalizedCode
  simp only [forcingIterationCode_val U, forcingNormalizationCarriers_val U, forcingNormalizationOrders_val U, forcingNormalizationProjections_val U, forcingNormalizationSections_val U, forcingNormalizationLifts_val U, forcingCodet_val U]

theorem forcingRecodedCode_val (θ s Q T m : SetDomain U) :
    (forcingRecodedCode θ s Q T m).val = forcingRecodedCode θ.val s.val Q.val T.val m.val := by
  unfold forcingRecodedCode
  simp only [forcingIterationCode_val U, forcingRecodedProjections_val U, forcingRecodedSections_val U, forcingRecodedLifts_val U, forcingRecodedTops_val U]

end TransitiveZF
end ZFVP


