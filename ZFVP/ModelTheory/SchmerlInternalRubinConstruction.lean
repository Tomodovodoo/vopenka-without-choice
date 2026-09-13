import ZFVP.ModelTheory.SchmerlInternalFirstRubinClause
import ZFVP.ModelTheory.SchmerlInternalRubinFilters

/-! The actual internal Rubin construction under diamond. Every
successor, the full bounded transfinite recursion, the clubs, and both
Rubin clauses are supplied by proved constructions. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internalRubinChain_isCodedRubin (hAC : InternalChoice V) (hω : HasStandardOmega V)
    {A M₀ C : V} (hA : IsInternalDiamondSequence A (hartogsNumber (ω : V)))
    (hC : C ∈ boundedBinaryModelCodes (hartogsNumber (ω : V)) ^ hartogsNumber (ω : V))
    (hrows : ∀ α ∈ hartogsNumber (ω : V), RubinRow A M₀ α C (C ‘ α)) :
    IsCodedRubin (codedBinaryChainUnion (hartogsNumber (ω : V)) C) (hartogsNumber (ω : V)) :=
  ⟨internalRubinChain_firstRubinClause hAC hω hC hrows,
    fun _ _ hP hR hpos _ hF hc ↦ internalRubinChain_definableFilters hAC hA hC hrows hP hR hpos hF hc⟩

theorem internalRubinChain_source (hAC : InternalChoice V) (hω : HasStandardOmega V)
    {A M₀ C : V} (hA : IsInternalDiamondSequence A (hartogsNumber (ω : V)))
    (hC : C ∈ boundedBinaryModelCodes (hartogsNumber (ω : V)) ^ hartogsNumber (ω : V))
    (hrows : ∀ α ∈ hartogsNumber (ω : V), RubinRow A M₀ α C (C ‘ α)) :
    IsCodedRubinFinSmallSource (codedBinaryChainUnion (hartogsNumber (ω : V)) C) := by
  obtain ⟨hchain, hZF, hfinite, _, _⟩ := internalRubinChain_union hC hrows
  refine ⟨⟨_, _, rfl, hchain.edges_subset⟩, hZF, ?_,
    internalRubinChain_isCodedRubin hAC hω hA hC hrows, hfinite⟩
  simp only [codedBinaryChainUnion, binaryRelationStructureCode_domain, internalRubinChain_carrier hrows]
  exact CardLE.refl _

/-- A countable binary coded model has an actual Rubin fin-small elementary
extension on the first uncountable ordinal. No ambient external countability
or supplied successor/chain/club witness is assumed. -/
theorem exists_codedRubinFinSmall_extension_of_internalDiamond
    (hAC : InternalChoice V) (hω : HasStandardOmega V) (hdiamond : InternalDiamond V)
    {D E : V} (hM : IsCodedZFModel (binaryRelationStructureCode D E))
    (hcount : IsInternallyCountable D) :
    ∃ N e : V, IsCodedRubinFinSmallSource N ∧
      IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode D E) N e ∧
      structureDomain N = hartogsNumber (ω : V) := by
  obtain ⟨A, hA⟩ := hdiamond
  obtain ⟨M₀, hM₀, h, _, _, _, hZF₀, hcount₀, he⟩ :=
    exists_hartogsOmega_normalized_codedZF hM hcount
  obtain ⟨C, hC, hrows⟩ := exists_internalRubinChain hAC hω hM₀ hZF₀ hcount₀ A
  refine ⟨codedBinaryChainUnion (hartogsNumber (ω : V)) C,
    compose h (SetTheory.identity (structureDomain M₀)), internalRubinChain_source hAC hω hA hC hrows,
    he.comp (internalRubinChain_union hC hrows).2.2.2.1, ?_⟩
  simpa only [codedBinaryChainUnion, binaryRelationStructureCode_domain] using internalRubinChain_carrier hrows

theorem exists_codedRubinFinSmall_source_of_internalDiamond
    (hAC : InternalChoice V) (hω : HasStandardOmega V) (hdiamond : InternalDiamond V)
    {D E : V} (hM : IsCodedZFModel (binaryRelationStructureCode D E))
    (hcount : IsInternallyCountable D) : ∃ N : V, IsCodedRubinFinSmallSource N := by
  obtain ⟨N, _, hN, _, _⟩ := exists_codedRubinFinSmall_extension_of_internalDiamond hAC hω hdiamond hM hcount
  exact ⟨N, hN⟩

end ZFVP.Schmerl
