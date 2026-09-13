import ZFVP.ModelTheory.WoodinSupportSuccessorMap
import ZFVP.ModelTheory.WoodinActualSuccessorMaps

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V}
local notation "C" => woodinNormalizedStageCode (succ θ)
local notation "D" => woodinNormalizedStageCode θ
local notation "A" => woodinNormalizedSupportCodes θ
local notation "B" => woodinNormalizedSupportOrder θ
local notation "top" => woodinNormalizedSupportTop θ
local notation "f" => woodinNormalizedSupportEncode θ

theorem woodinSupportSuccessorMap_section {i p : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hi : i ∈ succ θ) (hp : p ∈ (forcingCodeP D) ‘ i) :
    (woodinSupportSuccessorMap θ) ‘ (((forcingCodeE C) ‘ ⟨i, succ θ⟩ₖ) ‘ p) =
      ⟨f ‘ (((forcingCodeE D) ‘ ⟨i, θ⟩ₖ) ‘ p), ∅⟩ₖ := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hθ
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hc := woodinNormalizedStageCode_valid hΩ hAC (hΩ.inaccessible.rankCriterion.2.2.1 θ hθ)
  have hp' : p ∈ (forcingCodeP C) ‘ i := by
    rwa [woodinNormalizedStage_successor_old_carrier hΩ hAC hθ hi]
  have hz := function_value_mem
    (hc.system.functions.sectionMap i (mem_succ_iff.mpr (Or.inr hi))
      (succ θ) (mem_succ_self (succ θ)) (IsOrdinal.toIsTransitive.transitive _ hi)) hp'
  rw [woodinSupportSuccessorMap_value hΩ hAC hθ h0 hlim hinac hz,
    woodinNormalizedStage_successor_section hΩ hAC hθ hi hp,
    normalizedTwoStepIsoValue_empty_tail (woodinNormalizedSupportOrder_preorder hΩ hAC hsub)
      (woodinNormalizedSupportTop_spec hΩ hAC hθ h0 hlim hinac).1]

theorem woodinSupportSuccessorMap_lift {i z p : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hi : i ∈ succ θ) (hz : z ∈ (forcingCodeP C) ‘ (succ θ))
    (hp : p ∈ (forcingCodeP D) ‘ i)
    (hle : ⟨p, ((forcingCodeπ C) ‘ ⟨i, succ θ⟩ₖ) ‘ z⟩ₖ ∈ (forcingCodeR C) ‘ i) :
    (woodinSupportSuccessorMap θ) ‘ (((forcingCodeL C) ‘ ⟨i, succ θ⟩ₖ) ‘ ⟨z, p⟩ₖ) =
      ⟨f ‘ (((forcingCodeL D) ‘ ⟨i, θ⟩ₖ) ‘ ⟨kpair.π₁ z, p⟩ₖ),
        kpair.π₂ ((woodinSupportSuccessorMap θ) ‘ z)⟩ₖ := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hθ
  have hc := woodinNormalizedStageCode_valid hΩ hAC (hΩ.inaccessible.rankCriterion.2.2.1 θ hθ)
  have hp' : p ∈ (forcingCodeP C) ‘ i := by
    rwa [woodinNormalizedStage_successor_old_carrier hΩ hAC hθ hi]
  have hl := (hc.system.lifts.lift i (mem_succ_iff.mpr (Or.inr hi))
    (succ θ) (mem_succ_self (succ θ)) (IsOrdinal.toIsTransitive.transitive _ hi) z hz p hp' hle).1
  rw [woodinSupportSuccessorMap_value hΩ hAC hθ h0 hlim hinac hl,
    woodinNormalizedStage_successor_lift hΩ hAC hθ hi hz hp,
    woodinSupportSuccessorMap_value hΩ hAC hθ h0 hlim hinac hz]
  simp only [normalizedTwoStepIsoValue, kpair.π₁_kpair, kpair.π₂_kpair]

end ZFVP
