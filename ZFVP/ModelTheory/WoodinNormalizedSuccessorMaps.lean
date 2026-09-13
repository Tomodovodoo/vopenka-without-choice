import ZFVP.ModelTheory.WoodinNormalizedSuccessorCanonical

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω k s K m : V} [IsOrdinal k]
local notation "s'" => woodinIterationSuccessor k s K
local notation "m'" => woodinNormalizationSuccessor k s K m
local notation "C" => forcingNormalizedCode (succ (succ k)) s' m'
local notation "D" => forcingNormalizedCode (succ k) s m

omit [IsOrdinal k] in
theorem woodinNormalizedSuccessor_old_carrier {i : V} (hi : i ∈ succ k) :
    (forcingCodeP C) ‘ i = (forcingCodeP D) ‘ i := by
  simp only [forcingNormalizedCode, forcingCodeP_code,
    forcingNormalizationCarriers_value hi,
    forcingNormalizationCarriers_value (mem_succ_iff.mpr (Or.inr hi)),
    woodinNormalizationSuccessor_old hi, woodinIterationSuccessor, forcingSuccessorCode,
    forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_old hi]

omit [IsOrdinal k] in
theorem woodinNormalizedSuccessor_top :
    (forcingCodet C) ‘ (succ k) = ⟨(forcingCodet D) ‘ k, ∅⟩ₖ := by
  simp only [forcingNormalizedCode, forcingCodet_code,
    woodinIterationSuccessor, forcingSuccessorCode_top]

theorem woodinNormalizedSuccessor_projection {i z : V}
    (hΩ : IsWoodinSupercompact Ω) (hs : IsWoodinIteration Ω (succ k) s K)
    (hm : IsForcingNormalizationFamily (succ k) s m)
    (hi : i ∈ succ k) (hz : z ∈ (forcingCodeP C) ‘ (succ k)) :
    ((forcingCodeπ C) ‘ ⟨i, succ k⟩ₖ) ‘ z = ((forcingCodeπ D) ‘ ⟨i, k⟩ₖ) ‘ (kpair.π₁ z) := by
  have hm' := woodinNormalizationSuccessor_family hΩ hs hm
  have hs' := hs.successor hΩ
  have hi' : i ∈ succ (succ k) := mem_succ_iff.mpr (Or.inr hi)
  have hik : i ⊆ k := by
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ hi
  have hiz : i ⊆ succ k := IsOrdinal.toIsTransitive.transitive _ hi
  have hzN : z ∈ (forcingNormalizationCarriers (succ (succ k)) s' m') ‘ (succ k) := by
    simpa only [forcingNormalizedCode, forcingCodeP_code] using hz
  have hzP := hm'.inclusion (succ k) (mem_succ_self (succ k)) z hzN
  have hfirst : kpair.π₁ z ∈ (forcingNormalizationCarriers (succ k) s m) ‘ k := by
    have he := (woodinNormalizedSuccessor_carrier_order hΩ hs hm).1
    rw [he] at hz
    obtain ⟨p, hp, τ, _, rfl⟩ := mem_prod_iff.mp hz
    simpa only [kpair.π₁_kpair, forcingNormalizationCarriers_value (mem_succ_self k)] using hp
  simp only [forcingNormalizedCode, forcingCodeπ_code]
  rw [forcingNormalizationProjections_apply hm' hs'.code hi' (mem_succ_self (succ k)) hiz hzN,
    forcingNormalizationProjections_apply hm hs.code hi (mem_succ_self k) hik hfirst]
  exact woodinIterationSuccessor_projection_value hi hzP

theorem woodinNormalizedSuccessor_section {i p : V}
    (hΩ : IsWoodinSupercompact Ω) (hs : IsWoodinIteration Ω (succ k) s K)
    (hm : IsForcingNormalizationFamily (succ k) s m)
    (hi : i ∈ succ k) (hp : p ∈ (forcingCodeP D) ‘ i) :
    ((forcingCodeE C) ‘ ⟨i, succ k⟩ₖ) ‘ p = ⟨((forcingCodeE D) ‘ ⟨i, k⟩ₖ) ‘ p, ∅⟩ₖ := by
  have hm' := woodinNormalizationSuccessor_family hΩ hs hm
  have hs' := hs.successor hΩ
  have hi' : i ∈ succ (succ k) := mem_succ_iff.mpr (Or.inr hi)
  have hik : i ⊆ k := by
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ hi
  have hiz : i ⊆ succ k := IsOrdinal.toIsTransitive.transitive _ hi
  have hpN : p ∈ (forcingNormalizationCarriers (succ k) s m) ‘ i := by
    simpa only [forcingNormalizedCode, forcingCodeP_code] using hp
  have hpN' : p ∈ (forcingNormalizationCarriers (succ (succ k)) s' m') ‘ i := by
    have hpc : p ∈ (forcingCodeP C) ‘ i := (woodinNormalizedSuccessor_old_carrier hi).symm ▸ hp
    simpa only [forcingNormalizedCode, forcingCodeP_code] using hpc
  simp only [forcingNormalizedCode, forcingCodeE_code]
  rw [forcingNormalizationSections_apply hm' hs'.code hi' (mem_succ_self (succ k)) hiz hpN',
    forcingNormalizationSections_apply hm hs.code hi (mem_succ_self k) hik hpN]
  exact woodinIterationSuccessor_section_value hi (hm.inclusion i hi p hpN)

theorem woodinNormalizedSuccessor_lift {i z p : V}
    (hΩ : IsWoodinSupercompact Ω) (hs : IsWoodinIteration Ω (succ k) s K)
    (hm : IsForcingNormalizationFamily (succ k) s m)
    (hi : i ∈ succ k) (hz : z ∈ (forcingCodeP C) ‘ (succ k))
    (hp : p ∈ (forcingCodeP D) ‘ i) :
    ((forcingCodeL C) ‘ ⟨i, succ k⟩ₖ) ‘ ⟨z, p⟩ₖ =
      ⟨((forcingCodeL D) ‘ ⟨i, k⟩ₖ) ‘ ⟨kpair.π₁ z, p⟩ₖ, kpair.π₂ z⟩ₖ := by
  have hm' := woodinNormalizationSuccessor_family hΩ hs hm
  have hi' : i ∈ succ (succ k) := mem_succ_iff.mpr (Or.inr hi)
  have hzN : z ∈ (forcingNormalizationCarriers (succ (succ k)) s' m') ‘ (succ k) := by
    simpa only [forcingNormalizedCode, forcingCodeP_code] using hz
  have hpN : p ∈ (forcingNormalizationCarriers (succ k) s m) ‘ i := by
    simpa only [forcingNormalizedCode, forcingCodeP_code] using hp
  have hpN' : p ∈ (forcingNormalizationCarriers (succ (succ k)) s' m') ‘ i := by
    have hpc : p ∈ (forcingCodeP C) ‘ i := (woodinNormalizedSuccessor_old_carrier hi).symm ▸ hp
    simpa only [forcingNormalizedCode, forcingCodeP_code] using hpc
  have hzP := hm'.inclusion (succ k) (mem_succ_self (succ k)) z hzN
  have hpP := hm.inclusion i hi p hpN
  have hfirst : kpair.π₁ z ∈ (forcingNormalizationCarriers (succ k) s m) ‘ k := by
    rw [(woodinNormalizedSuccessor_carrier_order hΩ hs hm).1] at hz
    obtain ⟨q, hq, τ, _, rfl⟩ := mem_prod_iff.mp hz
    simpa only [kpair.π₁_kpair, forcingNormalizationCarriers_value (mem_succ_self k)] using hq
  simp only [forcingNormalizedCode, forcingCodeL_code]
  rw [forcingNormalizationLifts_apply hi' (mem_succ_self (succ k)) hzN hpN',
    forcingNormalizationLifts_apply hi (mem_succ_self k) hfirst hpN]
  simp only [woodinIterationSuccessor, forcingSuccessorCode, forcingIterationCodeNext,
    forcingCodeL_code, forcingMatrixNext_column hi]
  simp only [woodinIterationSuccessor, forcingSuccessorCode_poset] at hzP
  rw [successorLiftColumn_value hi hzP hpP]
  simp only [successorForcingLiftValue, twoStepStronger]

theorem woodinNormalizedStage_successor_top
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω) :
    (forcingCodet (woodinNormalizedStageCode (succ k))) ‘ (succ k) =
      ⟨(forcingCodet (woodinNormalizedStageCode k)) ‘ k, ∅⟩ₖ := by
  let := hΩ.inaccessible.1
  have hsub : succ k ⊆ Ω := by
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hk
    · exact IsOrdinal.toIsTransitive.mem_trans hi hk
  have hx := woodinIterationExit hΩ hAC
  have ht := woodinIterationPrefix_top_value
    (fun i hi ↦ (hx.2.1 i (hsub i hi)).1) (mem_succ_self k) (mem_succ_self k)
  simp only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodet_code,
    woodinIterationRec_successor, kpair.π₁_kpair, woodinIterationSuccessor, forcingSuccessorCode_top, ht]

end ZFVP
