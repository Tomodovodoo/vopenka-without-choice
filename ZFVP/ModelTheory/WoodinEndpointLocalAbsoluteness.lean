import ZFVP.ModelTheory.WoodinSourceEndpointAgreement
import ZFVP.ModelTheory.WoodinLocalPresentation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.rank_woodinStagePoset_val {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    letI := hδ.inaccessible.1
    letI := rankDomain_nonempty hδ.inaccessible.2.1
    letI := hδ.inaccessible.rankCriterion.models_zf
    ∀ i : SetDomain (hierarchy δ), IsOrdinal i →
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i).val =
        (forcingCodeP (kpair.π₁ (woodinIterationRec i.val))) ‘ i.val := by
  let := hδ.inaccessible.1
  let := rankDomain_nonempty hδ.inaccessible.2.1
  let := hδ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive δ
  intro i hi
  rw [TransitiveZF.value_val_total, TransitiveZF.forcingCodeP_val,
    TransitiveZF.kpair_first_val, hδ.rank_woodinIterationRec_val hAC i hi]

theorem IsWoodinSupercompact.rank_localStageCondition_iff {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    letI := hδ.inaccessible.1
    letI := rankDomain_nonempty hδ.inaccessible.2.1
    letI := hδ.inaccessible.rankCriterion.models_zf
    ∀ z : SetDomain (hierarchy δ), IsWoodinLocalStageCondition z ↔ IsWoodinLocalStageCondition z.val := by
  let := hδ.inaccessible.1
  let := rankDomain_nonempty hδ.inaccessible.2.1
  let := hδ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive δ
  intro z
  constructor
  · rintro ⟨i, p, hi, hp, hz⟩
    refine ⟨i.val, p.val, (TransitiveZF.ordinal_iff (hierarchy δ) i).mp hi, ?_, ?_⟩
    · change p.val ∈ ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i).val at hp
      rwa [hδ.rank_woodinStagePoset_val hAC i hi] at hp
    · simpa only [TransitiveZF.kpair_val] using congrArg Subtype.val hz
  · rintro ⟨i, p, hi, hp, hz⟩
    have hpair : ⟨i, p⟩ₖ ∈ hierarchy δ := hz ▸ z.property
    obtain ⟨hiδ, hpδ⟩ := kpair_components_mem_transitive hpair
    let a : SetDomain (hierarchy δ) := ⟨i, hiδ⟩
    let b : SetDomain (hierarchy δ) := ⟨p, hpδ⟩
    have ha : IsOrdinal a := (TransitiveZF.ordinal_iff (hierarchy δ) a).mpr hi
    refine ⟨a, b, ha, ?_, ?_⟩
    · change p ∈ ((forcingCodeP (kpair.π₁ (woodinIterationRec a))) ‘ a).val
      rwa [hδ.rank_woodinStagePoset_val hAC a ha]
    · apply Subtype.ext
      simpa only [TransitiveZF.kpair_val] using hz

theorem IsWoodinSupercompact.rank_localComparison_iff {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    letI := hδ.inaccessible.1
    letI := rankDomain_nonempty hδ.inaccessible.2.1
    letI := hδ.inaccessible.rankCriterion.models_zf
    ∀ i j k p q : SetDomain (hierarchy δ), IsOrdinal k →
      (WoodinLocalComparison i j k p q ↔ WoodinLocalComparison i.val j.val k.val p.val q.val) := by
  let := hδ.inaccessible.1
  let := rankDomain_nonempty hδ.inaccessible.2.1
  let := hδ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive δ
  intro i j k p q hk
  unfold WoodinLocalComparison
  change (⟨_, _⟩ₖ : SetDomain (hierarchy δ)).val ∈ (_ : SetDomain (hierarchy δ)).val ↔ _
  simp only [TransitiveZF.kpair_val, TransitiveZF.value_val_total,
    TransitiveZF.forcingCodeE_val, TransitiveZF.forcingCodeR_val, TransitiveZF.kpair_first_val,
    hδ.rank_woodinIterationRec_val hAC k hk]

/-- The rank's own local carrier formula defines the actual stage-code carrier. -/
theorem eval_woodinLocalStageConditionFormula_endpoint {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    letI := hδ.inaccessible.1
    letI := rankDomain_nonempty hδ.inaccessible.2.1
    letI := hδ.inaccessible.rankCriterion.models_zf
    ∀ z : SetDomain (hierarchy δ), woodinLocalStageConditionFormula.Evalb ![z] ↔
      z.val ∈ woodinStageCarrier δ := by
  let := hδ.inaccessible.1
  let := rankDomain_nonempty hδ.inaccessible.2.1
  let := hδ.inaccessible.rankCriterion.models_zf
  intro z
  exact (Defined.eval_iff ![z]).trans ((hδ.rank_localStageCondition_iff hAC z).trans
    ⟨fun hz ↦ (woodinIteration_stage_conditions_local_rank hδ hAC).mpr ⟨z.property, hz⟩,
      fun hz ↦ ((woodinIteration_stage_conditions_local_rank hδ hAC).mp hz).2⟩)

theorem IsWoodinLocalStageCondition.index_ordinal {z : V} (hz : IsWoodinLocalStageCondition z) :
    IsOrdinal (kpair.π₁ z) := by
  obtain ⟨i, p, hi, _, rfl⟩ := hz
  simpa only [kpair.π₁_kpair] using hi

theorem IsWoodinSupercompact.rank_localStageOrder_iff {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    letI := hδ.inaccessible.1
    letI := rankDomain_nonempty hδ.inaccessible.2.1
    letI := hδ.inaccessible.rankCriterion.models_zf
    ∀ z w : SetDomain (hierarchy δ), IsWoodinLocalStageCondition z → IsWoodinLocalStageCondition w →
      (WoodinLocalStageOrder z w ↔ WoodinLocalStageOrder z.val w.val) := by
  let := hδ.inaccessible.1
  let := rankDomain_nonempty hδ.inaccessible.2.1
  let := hδ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive δ
  intro z w hz hw
  have hzw := hδ.rank_localComparison_iff hAC (kpair.π₁ z) (kpair.π₁ w)
    (kpair.π₁ w) (kpair.π₂ z) (kpair.π₂ w) hw.index_ordinal
  have hwz := hδ.rank_localComparison_iff hAC (kpair.π₁ z) (kpair.π₁ w)
    (kpair.π₁ z) (kpair.π₂ z) (kpair.π₂ w) hz.index_ordinal
  have hs := TransitiveZF.subset_val_iff (hierarchy δ) (kpair.π₁ z) (kpair.π₁ w)
  have ht := TransitiveZF.subset_val_iff (hierarchy δ) (kpair.π₁ w) (kpair.π₁ z)
  simp only [TransitiveZF.kpair_first_val, TransitiveZF.kpair_second_val] at hzw hwz hs ht
  exact or_congr (and_congr hs hzw) (and_congr ht hwz)

/-- Carrier guards and the local comparison, all evaluated internally, recover
the actual endpoint order on stage codes. -/
theorem eval_woodinLocalStageOrderFormula_endpoint {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    letI := hδ.inaccessible.1
    letI := rankDomain_nonempty hδ.inaccessible.2.1
    letI := hδ.inaccessible.rankCriterion.models_zf
    ∀ z w : SetDomain (hierarchy δ),
      (woodinLocalStageConditionFormula.Evalb ![z] ∧ woodinLocalStageConditionFormula.Evalb ![w] ∧
        woodinLocalStageOrderFormula.Evalb ![z, w]) ↔
      ⟨z.val, w.val⟩ₖ ∈ woodinLocalOrderOn (woodinStageCarrier δ) := by
  let := hδ.inaccessible.1
  let := rankDomain_nonempty hδ.inaccessible.2.1
  let := hδ.inaccessible.rankCriterion.models_zf
  intro z w
  rw [mem_woodinLocalOrderOn_iff]
  have hz := eval_woodinLocalStageConditionFormula_endpoint hδ hAC z
  have hw := eval_woodinLocalStageConditionFormula_endpoint hδ hAC w
  constructor
  · rintro ⟨hc, hd, ho⟩
    exact ⟨hz.mp hc, hw.mp hd, (hδ.rank_localStageOrder_iff hAC z w
      ((Defined.eval_iff ![z]).mp hc) ((Defined.eval_iff ![w]).mp hd)).mp
        ((Defined.eval_iff ![z, w]).mp ho)⟩
  · rintro ⟨hc, hd, ho⟩
    have hzc := hz.mpr hc
    have hwc := hw.mpr hd
    exact ⟨hzc, hwc, (Defined.eval_iff ![z, w]).mpr
      ((hδ.rank_localStageOrder_iff hAC z w ((Defined.eval_iff ![z]).mp hzc)
        ((Defined.eval_iff ![w]).mp hwc)).mpr ho)⟩

end ZFVP
