import ZFVP.ModelTheory.SchmerlRubinRowExtension
import ZFVP.ModelTheory.SchmerlInternalCarrierAgreementClub
import ZFVP.SetTheory.BoundedHistoryRecursion

/-! The Rubin chain is an actual function of length hartogs(ω), obtained
by bounded Choice and internal transfinite recursion. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local irreducible] boundedBinaryModelCodes hartogsNumber

theorem exists_internalRubinChain (hAC : InternalChoice V) (hω : HasStandardOmega V)
    {M₀ : V} (hM : M₀ ∈ boundedBinaryModelCodes (hartogsNumber (ω : V)))
    (hZF : IsCodedZFModel M₀) (hc : IsInternallyCountable (structureDomain M₀)) (A : V) :
    ∃ C ∈ boundedBinaryModelCodes (hartogsNumber (ω : V)) ^ hartogsNumber (ω : V),
      ∀ α ∈ hartogsNumber (ω : V), RubinRow A M₀ α C (C ‘ α) := by
  let κ := hartogsNumber (ω : V)
  let B := boundedBinaryModelCodes κ
  let Next : V → V → Prop := fun s M ↦ RubinRow A M₀ (domain s) s M
  have hrdef := rubinRow_definable A M₀
  have hNext : ℒₛₑₜ-relation[V] Next := by unfold Next; definability
  obtain ⟨C, hC, hsel⟩ := exists_boundedHistoryRecursion (κ := κ) (B := B) hAC inferInstance hM Next hNext
  let : IsFunction C := IsFunction.of_mem hC
  have hvalue {α β : V} (hα : α ∈ κ) (hβα : β ∈ α) : (C ↾ α) ‘ β = C ‘ β :=
    value_restrict (by rw [domain_eq_of_mem_function hC]; exact IsOrdinal.toIsTransitive.mem_trans hβα hα) hβα
  have hall : ∀ α : Ordinal V, (α : V) ∈ κ → RubinRow A M₀ α C (C ‘ α) := by
    apply transfinite_induction (fun α : V ↦ α ∈ κ → RubinRow A M₀ α C (C ‘ α)) (by definability)
    intro α ih hα
    have hpast : ∀ β ∈ (α : V), RubinRow A M₀ β (C ↾ (α : V)) ((C ↾ (α : V)) ‘ β) := by
      intro β hβ
      let : IsOrdinal β := IsOrdinal.of_mem hβ
      have hβκ : β ∈ κ := IsOrdinal.toIsTransitive.mem_trans hβ hα
      have hh := ih (IsOrdinal.toOrdinal β) hβ hβκ
      rw [hvalue hα hβ]
      apply hh.congr
      intro γ hγ
      exact (hvalue hα (IsOrdinal.toIsTransitive.mem_trans hγ hβ)).symm
    have hp := hsel (α : V) hα
    obtain ⟨M, hrow⟩ := exists_rubinRow hAC hω hα hM hZF hc
      (IsFunction.of_mem hp.1) hp.2.1 hpast
    have hn : Next (C ↾ (α : V)) (C ‘ (α : V)) := hp.2.2.1 ⟨M, hrow.bounded, by
      change RubinRow A M₀ (domain (C ↾ (α : V))) (C ↾ (α : V)) M
      rwa [hp.2.1]⟩
    change RubinRow A M₀ (domain (C ↾ (α : V))) (C ↾ (α : V)) (C ‘ (α : V)) at hn
    rw [hp.2.1] at hn
    exact hn.congr (fun β hβ ↦ hvalue hα hβ)
  refine ⟨C, hC, fun α hα ↦ ?_⟩
  let : IsOrdinal α := IsOrdinal.of_mem hα
  exact hall (IsOrdinal.toOrdinal α) hα

theorem internalRubinChain_cover {A M₀ C : V}
    (hrows : ∀ α ∈ hartogsNumber (ω : V), RubinRow A M₀ α C (C ‘ α)) :
    ∀ β ∈ hartogsNumber (ω : V), β ∈ structureDomain (C ‘ (succ β)) := by
  intro β hβ
  exact ((hrows (succ β) (hartogsNumber_succ_mem (CardLE.refl _) hβ)).successor
    β (mem_succ_self β) rfl).1

theorem internalRubinChain_bounds {A M₀ C : V}
    (hrows : ∀ α ∈ hartogsNumber (ω : V), RubinRow A M₀ α C (C ‘ α)) :
    ∀ β ∈ hartogsNumber (ω : V), ∃ c,
      IsCodedCofinalBounds (C ‘ β) (C ‘ (succ β)) (SetTheory.identity (structureDomain (C ‘ β))) c := by
  intro β hβ
  exact ((hrows (succ β) (hartogsNumber_succ_mem (CardLE.refl _) hβ)).successor
    β (mem_succ_self β) rfl).2

theorem internalRubinChain_carrier {A M₀ C : V}
    (hrows : ∀ α ∈ hartogsNumber (ω : V), RubinRow A M₀ α C (C ‘ α)) :
    codedChainCarrier (hartogsNumber (ω : V)) C = hartogsNumber (ω : V) := by
  apply SetTheory.subset_antisymm
  · intro x hx
    obtain ⟨β, hβ, hx⟩ := (mem_codedChainCarrier _ _ _).mp hx
    exact boundedBinaryModelCodes_domain_subset (hrows β hβ).bounded x hx
  · intro β hβ
    exact codedChainCarrier_includes (hartogsNumber_succ_mem (CardLE.refl _) hβ) β
      (internalRubinChain_cover hrows β hβ)

theorem internalRubinChain_continuous {A M₀ C : V}
    (hrows : ∀ α ∈ hartogsNumber (ω : V), RubinRow A M₀ α C (C ‘ α)) :
    ∀ α ∈ hartogsNumber (ω : V), IsLimitOrdinal α → ∀ x,
      x ∈ structureDomain (C ‘ α) ↔ ∃ β ∈ α, x ∈ structureDomain (C ‘ β) := by
  intro α hα hlim x
  rw [(hrows α hα).limit hlim]
  simp only [codedBinaryChainUnion, binaryRelationStructureCode_domain, mem_codedChainCarrier]

theorem internalRubinChain_union {A M₀ C : V}
    (hC : C ∈ boundedBinaryModelCodes (hartogsNumber (ω : V)) ^ hartogsNumber (ω : V))
    (hrows : ∀ α ∈ hartogsNumber (ω : V), RubinRow A M₀ α C (C ‘ α)) :
    IsInternalRelationalChain membershipLanguageCode (hartogsNumber (ω : V)) C ∧
      IsCodedZFModel (codedBinaryChainUnion (hartogsNumber (ω : V)) C) ∧
      IsCodedFinSmall (codedBinaryChainUnion (hartogsNumber (ω : V)) C) ∧
      IsCodedElementaryInclusion M₀ (codedBinaryChainUnion (hartogsNumber (ω : V)) C) ∧
      ∀ β ∈ hartogsNumber (ω : V),
        IsCodedInseparable (C ‘ β) (guessedU A C β) (guessedW A C β) →
          IsCodedInseparable (codedBinaryChainUnion (hartogsNumber (ω : V)) C)
            (guessedU A C β) (guessedW A C β) := by
  have hκne : IsNonempty (hartogsNumber (ω : V)) := ⟨ω, omega_mem_hartogs_omega⟩
  have hchain := rubinRows_chain inferInstance hκne (IsFunction.of_mem hC) (domain_eq_of_mem_function hC) hrows
  have heq : ∀ β ∈ hartogsNumber (ω : V),
      (structureRelations (C ‘ β)) ‘ (0 : V) = equalityRelation (structureDomain (C ‘ β)) := by
    intro β hβ
    obtain ⟨D, E, _, _, hh⟩ := mem_boundedBinaryModelCodes.mp (hrows β hβ).bounded
    simp only [hh, binaryRelationStructureCode_equality, binaryRelationStructureCode_domain]
  have hEq : codedChainUnion membershipLanguageCode (hartogsNumber (ω : V)) C =
      codedBinaryChainUnion (hartogsNumber (ω : V)) C := hchain.union_eq_binaryRelationStructureCode heq
  have hzero : (∅ : V) ∈ hartogsNumber (ω : V) := IsOrdinal.empty_mem_iff_nonempty.mpr hκne
  have hinit := (hrows ∅ hzero).initial rfl
  have hfinite := rubinRows_finite (inferInstance : IsOrdinal (hartogsNumber (ω : V))) hrows
  have hpres := rubinRows_guesses (inferInstance : IsOrdinal (hartogsNumber (ω : V))) hrows
  refine ⟨hchain, hEq ▸ hchain.union_codedZF hzero (hrows ∅ hzero).model,
    hEq ▸ hchain.union_finSmall (fun β hβ ↦ (hrows β hβ).countable) hfinite, ?_, ?_⟩
  · simpa only [hinit, IsCodedElementaryInclusion, codedBinaryChainUnion] using
      hchain.stage_elementary_binaryUnion heq hzero
  · intro β hβ hacc
    exact hchain.union_inseparable_binary hβ (fun γ hγ hβγ ↦ hpres β hβ γ hγ hβγ hacc) heq

theorem internalRubinChain_stageInclusion {A M₀ C : V}
    (hC : C ∈ boundedBinaryModelCodes (hartogsNumber (ω : V)) ^ hartogsNumber (ω : V))
    (hrows : ∀ α ∈ hartogsNumber (ω : V), RubinRow A M₀ α C (C ‘ α))
    {β : V} (hβ : β ∈ hartogsNumber (ω : V)) :
    IsCodedElementaryInclusion (C ‘ β) (codedBinaryChainUnion (hartogsNumber (ω : V)) C) := by
  exact (internalRubinChain_union hC hrows).1.stage_elementary_binaryUnion_of_binary_stages
    (fun α hα ↦ by
      obtain ⟨D, E, _, _, he⟩ := mem_boundedBinaryModelCodes.mp (hrows α hα).bounded
      exact ⟨D, E, he⟩) hβ

theorem internalRubinChain_carrierAgreement (hAC : InternalChoice V) {A M₀ C : V}
    (hC : C ∈ boundedBinaryModelCodes (hartogsNumber (ω : V)) ^ hartogsNumber (ω : V))
    (hrows : ∀ α ∈ hartogsNumber (ω : V), RubinRow A M₀ α C (C ‘ α)) :
    ∃ E : V, IsClubIn E (hartogsNumber (ω : V)) ∧
      ∀ α ∈ E, IsLimitOrdinal α ∧ structureDomain (C ‘ α) = α :=
  exists_codedCarrierAgreementClub hAC (fun α hα ↦ (hrows α hα).countable)
    (fun α hα ↦ boundedBinaryModelCodes_domain_subset (hrows α hα).bounded)
    (internalRubinChain_union hC hrows).1.increasing
    (internalRubinChain_continuous hrows) (internalRubinChain_cover hrows)

end ZFVP.Schmerl
