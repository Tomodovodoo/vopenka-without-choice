import ZFVP.ModelTheory.WoodinInverseSourceMaps
import ZFVP.ModelTheory.WoodinNormalizedInverseBase

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ s K m : V}

theorem woodinNormalizedInverse_old_carrier {i : V} (hi : i ∈ θ) :
    (forcingCodeP (forcingNormalizedCode (succ θ) (woodinInverseSourceCode θ s K)
      (woodinNormalizationInverse θ s K m))) ‘ i =
    (forcingCodeP (forcingNormalizedCode θ s m)) ‘ i := by
  simp only [forcingNormalizedCode, forcingCodeP_code,
    forcingNormalizationCarriers_value hi,
    forcingNormalizationCarriers_value (mem_succ_iff.mpr (Or.inr hi)),
    woodinNormalizationInverse_old hi, woodinInverseSourceCode_twoStepColumn,
    forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_old hi]

variable {Ω : V} [IsOrdinal θ]
local notation "S" => woodinIterationPrefix θ
local notation "M" => woodinNormalizationHistory θ
local notation "C" => woodinNormalizedStageCode θ
local notation "D" => woodinNormalizedPrefixCode θ
local notation "γ" => woodinLimitCardinal (woodinIterationCardinalPrefix θ)

omit [IsOrdinal θ] in
theorem woodinNormalizedInverse_old_order {i : V} (hi : i ∈ θ) :
    (forcingCodeR (forcingNormalizedCode (succ θ) (woodinInverseSourceCode θ s K)
      (woodinNormalizationInverse θ s K m))) ‘ i =
    (forcingCodeR (forcingNormalizedCode θ s m)) ‘ i := by
  simp only [forcingNormalizedCode, forcingCodeR_code,
    forcingNormalizationOrders_value hi,
    forcingNormalizationOrders_value (mem_succ_iff.mpr (Or.inr hi)),
    forcingNormalizationCarriers_value hi,
    forcingNormalizationCarriers_value (mem_succ_iff.mpr (Or.inr hi)),
    woodinNormalizationInverse_old hi, woodinInverseSourceCode_twoStepColumn,
    forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeP_code, forcingCodeR_code,
    forcingFamilyNext_old hi]

theorem woodinNormalizedStage_inverse_code
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ) :
    C = forcingNormalizedCode (succ θ) (woodinInverseSourceCode θ S (woodinIterationCardinalPrefix θ))
      (woodinNormalizationInverse θ S (woodinIterationCardinalPrefix θ) M) := by
  simp only [woodinNormalizedStageCode, woodinIterationRec_inverse h0 hlim hn,
    kpair.π₁_kpair, woodinNormalizationHistory_inverse h0 hlim hn]

theorem woodinNormalizedStage_inverse_old_carrier {i : V}
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ) (hi : i ∈ θ) :
    (forcingCodeP C) ‘ i = (forcingCodeP D) ‘ i := by
  rw [woodinNormalizedStage_inverse_code h0 hlim hn]
  exact woodinNormalizedInverse_old_carrier hi

theorem woodinNormalizedStage_inverse_top
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ) :
    (forcingCodet C) ‘ θ = ⟨forcingInverseCodeTop θ S, ∅⟩ₖ := by
  simp only [woodinNormalizedStage_inverse_code h0 hlim hn, forcingNormalizedCode,
    forcingCodet_code, woodinInverseSourceCode_top]

theorem woodinNormalizedStage_inverse_old_order {i : V}
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ) (hi : i ∈ θ) :
    (forcingCodeR C) ‘ i = (forcingCodeR D) ‘ i := by
  rw [woodinNormalizedStage_inverse_code h0 hlim hn]
  exact woodinNormalizedInverse_old_order hi

theorem woodinNormalizedStage_inverse_projection {i z : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ)
    (hi : i ∈ θ) (hz : z ∈ (forcingCodeP C) ‘ θ) :
    ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) ‘ z = (kpair.π₁ z) ‘ i := by
  have hm := woodinNormalizationHistory_family hΩ hAC θ hθ
  have hs := ((woodinIterationExit hΩ hAC).2.1 θ hθ).1.code
  have hzN : z ∈ (forcingNormalizationCarriers (succ θ) (kpair.π₁ (woodinIterationRec θ))
      (woodinNormalizationHistory (succ θ))) ‘ θ := by
    simpa only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodeP_code] using hz
  have hzP := hm.inclusion θ (mem_succ_self θ) z hzN
  simp only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodeπ_code]
  rw [forcingNormalizationProjections_apply hm hs (mem_succ_iff.mpr (Or.inr hi))
    (mem_succ_self θ) (IsOrdinal.toIsTransitive.transitive _ hi) hzN]
  rw [woodinIterationRec_inverse h0 hlim hn, kpair.π₁_kpair] at hzP ⊢
  exact woodinInverseSourceCode_projection hi hzP

theorem woodinNormalizedStage_inverse_section {i p : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ)
    (hi : i ∈ θ) (hp : p ∈ (forcingCodeP D) ‘ i) :
    ((forcingCodeE C) ‘ ⟨i, θ⟩ₖ) ‘ p = ⟨forcingSectionThread θ (forcingCodeπ S) (forcingCodeE S) i p, ∅⟩ₖ := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hx := woodinIterationExit hΩ hAC
  have hS := woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hsub i hi)).1)
  have hM := woodinNormalizationHistory_actual_prefix hΩ hAC hsub
  have hm := woodinNormalizationHistory_family hΩ hAC θ hθ
  have hs := (hx.2.1 θ hθ).1.code
  have hpC : p ∈ (forcingCodeP C) ‘ i := (woodinNormalizedStage_inverse_old_carrier h0 hlim hn hi).symm ▸ hp
  have hpN : p ∈ (forcingNormalizationCarriers (succ θ) (kpair.π₁ (woodinIterationRec θ))
      (woodinNormalizationHistory (succ θ))) ‘ i := by
    simpa only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodeP_code] using hpC
  have hpold : p ∈ (forcingNormalizationCarriers θ S M) ‘ i := by
    simpa only [woodinNormalizedPrefixCode, forcingNormalizedCode, forcingCodeP_code] using hp
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  simp only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodeE_code]
  rw [forcingNormalizationSections_apply hm hs (mem_succ_iff.mpr (Or.inr hi))
    (mem_succ_self θ) (IsOrdinal.toIsTransitive.transitive _ hi) hpN,
    woodinIterationRec_inverse h0 hlim hn, kpair.π₁_kpair]
  exact woodinInverseSourceCode_section hS.code hz hi (hM.inclusion i hi p hpold)

theorem woodinNormalizedStage_inverse_lift {i z p : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ)
    (hi : i ∈ θ) (hz : z ∈ (forcingCodeP C) ‘ θ) (hp : p ∈ (forcingCodeP D) ‘ i) :
    ((forcingCodeL C) ‘ ⟨i, θ⟩ₖ) ‘ ⟨z, p⟩ₖ =
      ⟨forcingThreadSplice θ (forcingCodeπ S) (forcingCodeL S) (kpair.π₁ z) i p, kpair.π₂ z⟩ₖ := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hM := woodinNormalizationHistory_actual_prefix hΩ hAC hsub
  have hm := woodinNormalizationHistory_family hΩ hAC θ hθ
  have hpC : p ∈ (forcingCodeP C) ‘ i := (woodinNormalizedStage_inverse_old_carrier h0 hlim hn hi).symm ▸ hp
  have hzN : z ∈ (forcingNormalizationCarriers (succ θ) (kpair.π₁ (woodinIterationRec θ))
      (woodinNormalizationHistory (succ θ))) ‘ θ := by
    simpa only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodeP_code] using hz
  have hpN : p ∈ (forcingNormalizationCarriers (succ θ) (kpair.π₁ (woodinIterationRec θ))
      (woodinNormalizationHistory (succ θ))) ‘ i := by
    simpa only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodeP_code] using hpC
  have hpold : p ∈ (forcingNormalizationCarriers θ S M) ‘ i := by
    simpa only [woodinNormalizedPrefixCode, forcingNormalizedCode, forcingCodeP_code] using hp
  have hzP := hm.inclusion θ (mem_succ_self θ) z hzN
  simp only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodeL_code]
  rw [forcingNormalizationLifts_apply (mem_succ_iff.mpr (Or.inr hi)) (mem_succ_self θ) hzN hpN]
  rw [woodinIterationRec_inverse h0 hlim hn, kpair.π₁_kpair] at hzP ⊢
  exact woodinInverseSourceCode_lift hi hzP (hM.inclusion i hi p hpold)

end ZFVP
