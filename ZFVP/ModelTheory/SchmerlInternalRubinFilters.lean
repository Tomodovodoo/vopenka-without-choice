import ZFVP.ModelTheory.SchmerlInternalRubinChain
import ZFVP.ModelTheory.SchmerlInternalDiamondCarrierGuess
import ZFVP.ModelTheory.SchmerlInternalNondefinabilityClub
import ZFVP.ModelTheory.SchmerlInternalIncompatibilityClub
import ZFVP.ModelTheory.SchmerlCodedInitialSegmentSeparator

/-! The second Rubin clause for the constructed actual chain. Diamond
meets three actual clubs, and the preserved guess contradicts the coded
initial segment supplied by a cofinal chain in the maximal family. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internalRubinChain_definableFilters (hAC : InternalChoice V) {A M₀ C : V}
    (hA : IsInternalDiamondSequence A (hartogsNumber (ω : V)))
    (hC : C ∈ boundedBinaryModelCodes (hartogsNumber (ω : V)) ^ hartogsNumber (ω : V))
    (hrows : ∀ α ∈ hartogsNumber (ω : V), RubinRow A M₀ α C (C ‘ α))
    {P R F : V}
    (hP : IsCodedDefinableSet (codedBinaryChainUnion (hartogsNumber (ω : V)) C) P)
    (hRdef : IsCodedDefinableRelation (codedBinaryChainUnion (hartogsNumber (ω : V)) C) R)
    (hR : IsForcingPoset P R) (hF : IsInternalMaximallyCompatible P R F)
    (hcof : ∃ c, IsInternalCofinalStrictChain (hartogsNumber (ω : V)) F R c) :
    IsCodedDefinableSet (codedBinaryChainUnion (hartogsNumber (ω : V)) C) F := by
  classical
  by_contra hnot
  let κ := hartogsNumber (ω : V)
  let N := codedBinaryChainUnion κ C
  have hN : structureDomain N = κ := by
    simpa only [N, κ, codedBinaryChainUnion, binaryRelationStructureCode_domain] using
      internalRubinChain_carrier hrows
  have hPκ : P ⊆ κ := hN ▸ hP.1
  have hFκ : F ⊆ κ := subset_trans hF.1 hPκ
  obtain ⟨E₀, hE₀, hD⟩ := internalRubinChain_carrierAgreement hAC hC hrows
  obtain ⟨E₁, hE₁, hreflect⟩ := exists_hartogsOmega_nondefinabilityClub hAC hN hFκ hnot
    (fun α hα ↦ internalRubinChain_stageInclusion hC hrows hα)
  obtain ⟨E₂, hE₂, hincomp⟩ := exists_hartogsOmega_incompatibilityClub hAC hF hPκ
  let E := (E₀ ∩ E₁) ∩ E₂
  have hE : IsClubIn E κ := club_inter (hartogsNumber_regular hAC (CardLE.refl _)) omega_mem_hartogs_omega
    (club_inter (hartogsNumber_regular hAC (CardLE.refl _)) omega_mem_hartogs_omega hE₀ hE₁) hE₂
  have hparts {α : V} (hα : α ∈ E) : α ∈ E₀ ∧ α ∈ E₁ ∧ α ∈ E₂ := by
    obtain ⟨h01, h2⟩ := mem_inter_iff.mp hα
    exact ⟨(mem_inter_iff.mp h01).1, (mem_inter_iff.mp h01).2, h2⟩
  obtain ⟨α, hακ, hαE, hU, hW⟩ := exists_internalDiamondCarrierGuess hA hFκ hE
    (fun α hα ↦ (hD α (hparts hα).1).2)
  have hacc : IsCodedInseparable (C ‘ α) (guessedU A C α) (guessedW A C α) := by
    rw [hU, hW]
    exact hreflect α (hparts hαE).2.1 (hD α (hparts hαE).1).2
  have hfull : IsCodedInseparable N (guessedU A C α) (guessedW A C α) :=
    (internalRubinChain_union hC hrows).2.2.2.2 α hακ hacc
  obtain ⟨c, hc⟩ := hcof
  have hUcount : IsInternallyCountable (guessedU A C α) := by
    rw [hU]
    exact internallyCountable_subset (countable_of_mem_hartogs_omega hακ) (fun _ hx ↦ (mem_inter_iff.mp hx).2)
  have hUF : guessedU A C α ⊆ F := by
    rw [hU]
    exact fun _ hx ↦ (mem_inter_iff.mp hx).1
  apply not_codedInseparable_of_countable_cofinalChain hAC hP hRdef hR hF hc hUcount hUF ?_ hfull
  intro q hq hqP
  rw [hW] at hq
  obtain ⟨hqα, hqF⟩ := mem_sdiff_iff.mp hq
  obtain ⟨u, hu, huq⟩ := (hincomp α (hparts hαE).2.2).2 q hqα hqP hqF
  exact ⟨u, hU.symm ▸ hu, huq⟩

end ZFVP.Schmerl
