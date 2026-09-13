import ZFVP.ModelTheory.ForcingNormalizedPrefix
import ZFVP.ModelTheory.WoodinNormalizedCode
import ZFVP.ModelTheory.WoodinPrefixCoordinates

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ η : V} [IsOrdinal θ]

theorem woodinNormalizedPrefix_extends [IsOrdinal η]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hη : η ⊆ Ω) (hθη : θ ⊆ η) :
    ForcingCodeExtends (woodinNormalizedPrefixCode θ) (woodinNormalizedPrefixCode η) := by
  have hθ := subset_trans hθη hη
  have hx := woodinIterationExit hΩ hAC
  apply forcingNormalized_extends
    (woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hθ i hi)).1)).code
    (woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hη i hi)).1)).code
    (woodinIterationPrefix_extends hθη) hθη
    (fun i hi ↦ ?_) (woodinNormalizedPrefixCode_valid hΩ hAC hθ)
    (woodinNormalizedPrefixCode_valid hΩ hAC hη)
  rw [woodinNormalizationHistory_value hi, woodinNormalizationHistory_value (hθη i hi)]

theorem woodinNormalizedPrefix_successor
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω) :
    woodinNormalizedPrefixCode (succ θ) = woodinNormalizedStageCode θ := by
  let := hΩ.inaccessible.1
  have hsub : succ θ ⊆ Ω := by
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hθ
    · exact IsOrdinal.toIsTransitive.transitive _ hθ i hi
  have hx := woodinIterationExit hΩ hAC
  have hh := woodinIterationHistory_of_stages (fun i hi ↦ (hx.2.1 i (hsub i hi)).1)
  unfold woodinNormalizedPrefixCode woodinNormalizedStageCode
  rw [(woodinIterationPrefix_successor hh).1]

theorem woodinNormalizedStage_extends
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω) :
    ForcingCodeExtends (woodinNormalizedPrefixCode θ) (woodinNormalizedStageCode θ) := by
  let := hΩ.inaccessible.1
  rw [← woodinNormalizedPrefix_successor hΩ hAC hθ]
  apply woodinNormalizedPrefix_extends hΩ hAC
  · intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hθ
    · exact IsOrdinal.toIsTransitive.transitive _ hθ i hi
  · exact fun i hi ↦ mem_succ_iff.mpr (Or.inr hi)

theorem woodinNormalizedStage_old_carrier_order {i : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω) (hi : i ∈ θ) :
    (forcingCodeP (woodinNormalizedStageCode θ)) ‘ i = (forcingCodeP (woodinNormalizedPrefixCode θ)) ‘ i ∧
    (forcingCodeR (woodinNormalizedStageCode θ)) ‘ i = (forcingCodeR (woodinNormalizedPrefixCode θ)) ‘ i := by
  let := hΩ.inaccessible.1
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hθ)
  have hz := woodinNormalizedStageCode_valid hΩ hAC hθ
  have he := woodinNormalizedStage_extends hΩ hAC hθ
  exact ⟨(hs.tableP.value_of_subset hz.tableP he.subP hi).symm,
    (hs.tableR.value_of_subset hz.tableR he.subR hi).symm⟩

end ZFVP
