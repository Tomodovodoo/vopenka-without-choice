import ZFVP.ModelTheory.SchmerlRubinRows

/-! Every valid countable bounded history has a next Rubin row. The
successor case uses the constructed omitting successor; the limit case
uses the actual coded chain union. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_rubinRow_zero {A M₀ C : V}
    (hM : M₀ ∈ boundedBinaryModelCodes (hartogsNumber (ω : V)))
    (hZF : IsCodedZFModel M₀) (hc : IsInternallyCountable (structureDomain M₀)) :
    RubinRow A M₀ ∅ C M₀ := by
  refine ⟨hM, hZF, hc, fun _ ↦ rfl, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | exact fun _ h ↦ (not_mem_empty h).elim | exact fun h ↦ (h.2.1 rfl).elim

theorem exists_rubinRow_successor (hAC : InternalChoice V) (hω : HasStandardOmega V)
    {A M₀ γ C : V} [IsOrdinal γ] (hγ : γ ∈ hartogsNumber (ω : V))
    (hcount : IsInternallyCountable (succ γ))
    (hrows : ∀ β ∈ succ γ, RubinRow A M₀ β C (C ‘ β)) :
    ∃ M, RubinRow A M₀ (succ γ) C M := by
  have hcur := hrows γ (mem_succ_self γ)
  let F := acceptedGuessFamily (succ γ) C A
  have hpres : PreservesAcceptedGuesses (succ γ) C A := rubinRows_guesses inferInstance hrows
  have hFcount : IsInternallyCountable F := acceptedGuessFamily_countable hcount
  have hF := hpres.family_subset_at_successor
  have hUW := hpres.family_at_successor
  obtain ⟨D, R, hDκ, hR, hcode⟩ := mem_boundedBinaryModelCodes.mp hcur.bounded
  have hmodel : IsCodedZFModel (binaryRelationStructureCode D R) := hcode ▸ hcur.model
  have hDcount : IsInternallyCountable D := by
    simpa only [hcode, binaryRelationStructureCode_domain] using hcur.countable
  have hF' : F ⊆ power D ×ˢ power D := by
    simpa only [hcode, binaryRelationStructureCode_domain] using hF
  have hUW' : ∀ U W, ⟨U, W⟩ₖ ∈ F → IsCodedInseparable (binaryRelationStructureCode D R) U W := by
    simpa only [hcode] using hUW
  obtain ⟨B, S, c, _, hBκ, hγB, hS, hBc, hBZ, he, hb, hf, hp⟩ :=
    exists_bounded_codedRubinSuccessor hAC hω hmodel hR hDκ hγ hDcount hFcount hF' hUW'
  let M := binaryRelationStructureCode B S
  have hinc : IsCodedElementaryInclusion (C ‘ γ) M := by
    simpa only [IsCodedElementaryInclusion, M, hcode, binaryRelationStructureCode_domain] using he
  have hfinite : IsCodedFiniteEndExtension (C ‘ γ) M := by simpa only [hcode] using hf
  refine ⟨M, ⟨binaryRelationStructureCode_mem_boundedBinaryModelCodes hBκ hS, hBZ,
    by simpa only [M, binaryRelationStructureCode_domain] using hBc, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro hzero
    exact (not_mem_empty (hzero ▸ mem_succ_self γ)).elim
  · intro β hβ
    rcases mem_succ_iff.mp hβ with rfl | hβ
    · exact hinc
    · exact (hcur.elementary β hβ).trans hinc
  · intro β hβ
    rcases mem_succ_iff.mp hβ with rfl | hβ
    · exact hfinite
    · exact (hcur.finite β hβ).trans (hcur.elementary β hβ) hinc hfinite
  · intro β hβ hacc
    exact hp _ _ ((pair_mem_acceptedGuessFamily _ _ _ _ _).mpr ⟨β, hβ, hacc, rfl, rfl⟩)
  · intro β hβ heq
    have hβγ : β = γ := by
      have hs : ⋃ˢ (succ γ) = ⋃ˢ (succ β) := congrArg sUnion heq
      let : IsOrdinal β := IsOrdinal.of_mem hβ
      simpa only [sUnion_succ_ordinal] using hs.symm
    subst β
    refine ⟨by simpa only [M, binaryRelationStructureCode_domain] using hγB, c, ?_⟩
    simpa only [hcode, binaryRelationStructureCode_domain] using hb
  · intro hlim
    exact (hlim.2.2 ⟨γ, rfl⟩).elim

theorem exists_rubinRow_limit (hAC : InternalChoice V) {A M₀ α C : V}
    (hlim : IsLimitOrdinal α) (hcount : IsInternallyCountable α)
    (hf : IsFunction C) (hd : domain C = α)
    (hrows : ∀ β ∈ α, RubinRow A M₀ β C (C ‘ β)) :
    RubinRow A M₀ α C (codedBinaryChainUnion α C) := by
  let : IsOrdinal α := hlim.1
  have hne : IsNonempty α := (eq_empty_or_isNonempty α).resolve_left hlim.2.1
  have hchain := rubinRows_chain hlim.1 hne hf hd hrows
  have heq : ∀ β ∈ α, (structureRelations (C ‘ β)) ‘ (0 : V) = equalityRelation (structureDomain (C ‘ β)) := by
    intro β hβ
    obtain ⟨D, E, _, _, hh⟩ := mem_boundedBinaryModelCodes.mp (hrows β hβ).bounded
    simp only [hh, binaryRelationStructureCode_equality, binaryRelationStructureCode_domain]
  have hEq : codedChainUnion membershipLanguageCode α C = codedBinaryChainUnion α C :=
    hchain.union_eq_binaryRelationStructureCode heq
  have hDκ : codedChainCarrier α C ⊆ hartogsNumber (ω : V) := by
    intro x hx
    obtain ⟨β, hβ, hx⟩ := (mem_codedChainCarrier _ _ _).mp hx
    exact boundedBinaryModelCodes_domain_subset (hrows β hβ).bounded x hx
  have hfreeze := rubinRows_finite hlim.1 hrows
  have hpres := rubinRows_guesses hlim.1 hrows
  obtain ⟨β₀, hβ₀⟩ := hne.nonempty
  refine ⟨binaryRelationStructureCode_mem_boundedBinaryModelCodes hDκ hchain.edges_subset,
    hEq ▸ hchain.union_codedZF hβ₀ (hrows β₀ hβ₀).model,
    ?_, ?_, ?_, ?_, ?_, ?_, fun _ ↦ rfl⟩
  · simpa only [codedBinaryChainUnion, binaryRelationStructureCode_domain] using
      codedChainCarrier_countable hAC hcount (fun β hβ ↦ (hrows β hβ).countable)
  · intro hz
    exact (hlim.2.1 hz).elim
  · intro β hβ
    exact hchain.stage_elementary_binaryUnion heq hβ
  · intro β hβ
    exact hchain.stage_finiteEndExtension_binary hfreeze heq hβ
  · intro β hβ hacc
    exact hchain.union_inseparable_binary hβ (fun γ hγ hβγ ↦ hpres β hβ γ hγ hβγ hacc) heq
  · intro β _ hs
    exact (hlim.2.2 ⟨β, hs⟩).elim

theorem exists_rubinRow (hAC : InternalChoice V) (hω : HasStandardOmega V)
    {A M₀ α C : V} (hα : α ∈ hartogsNumber (ω : V))
    (hM : M₀ ∈ boundedBinaryModelCodes (hartogsNumber (ω : V)))
    (hZF : IsCodedZFModel M₀) (hc : IsInternallyCountable (structureDomain M₀))
    (hf : IsFunction C) (hd : domain C = α)
    (hrows : ∀ β ∈ α, RubinRow A M₀ β C (C ‘ β)) : ∃ M, RubinRow A M₀ α C M := by
  let : IsOrdinal α := IsOrdinal.of_mem hα
  rcases ordinal_cases α with rfl | ⟨γ, hγo, rfl⟩ | hlim
  · exact ⟨M₀, exists_rubinRow_zero hM hZF hc⟩
  · let : IsOrdinal γ := hγo
    exact exists_rubinRow_successor hAC hω (IsOrdinal.toIsTransitive.mem_trans (mem_succ_self γ) hα)
      (countable_of_mem_hartogs_omega hα) hrows
  · exact ⟨_, exists_rubinRow_limit hAC hlim (countable_of_mem_hartogs_omega hα) hf hd hrows⟩

end ZFVP.Schmerl
