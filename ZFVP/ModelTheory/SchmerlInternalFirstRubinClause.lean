import ZFVP.ModelTheory.SchmerlCodedDirectedDefinitionTransfer
import ZFVP.ModelTheory.SchmerlInternalCofinalSequence
import ZFVP.ModelTheory.SchmerlInternalRubinChain

/-! The first Rubin clause follows from the actual elementary chain and its
successor bounds. The witness is an actual graph of least ordinal points. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsInternalRelationalChain.binaryUnion_bounded {κ C : V}
    (hchain : IsInternalRelationalChain membershipLanguageCode κ C)
    (hcarrier : codedChainCarrier κ C = κ) :
    codedBinaryChainUnion κ C ∈ boundedBinaryModelCodes κ :=
  binaryRelationStructureCode_mem_boundedBinaryModelCodes
    (by rw [hcarrier]) hchain.edges_subset

theorem IsInternalRelationalChain.directedIndex_eventual_stage (hω : HasStandardOmega V)
    {κ C u r : V} (hchain : IsInternalRelationalChain membershipLanguageCode κ C)
    (hC : C ∈ boundedBinaryModelCodes κ ^ κ) (hcarrier : codedChainCarrier κ C = κ)
    (hu : u ∈ unaryDefinitionParameters (codedBinaryChainUnion κ C))
    (hr : r ∈ binaryDefinitionParameters (codedBinaryChainUnion κ C))
    (hpos : IsForcingPoset (unaryDefinitionSet (codedBinaryChainUnion κ C) u)
      (binaryDefinitionRelation (codedBinaryChainUnion κ C) r))
    (hdir : IsInternalDirectedNoMax (unaryDefinitionSet (codedBinaryChainUnion κ C) u)
      (binaryDefinitionRelation (codedBinaryChainUnion κ C) r)) :
    ∃ β₀ ∈ κ, ∀ β ∈ κ, β₀ ⊆ β → ⟨u, r⟩ₖ ∈ codedDirectedPosetIndex (C ‘ β) := by
  obtain ⟨β₀, hβ₀, hdefs⟩ := hchain.definitions_eventual_stage
    (by simp only [codedBinaryChainUnion, binaryRelationStructureCode_domain]) hu hr
  have hbinary : ∀ β ∈ κ, ∃ D E, C ‘ β = binaryRelationStructureCode D E := by
    intro β hβ
    obtain ⟨D, E, _, _, he⟩ := mem_boundedBinaryModelCodes.mp (function_value_mem hC hβ)
    exact ⟨D, E, he⟩
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ hβ₀β
  obtain ⟨huβ, hrβ⟩ := hdefs β hβ hβ₀β
  have he : IsCodedElementaryInclusion (C ‘ β) (codedBinaryChainUnion κ C) :=
    hchain.stage_elementary_binaryUnion_of_binary_stages hbinary hβ
  exact (pair_mem_codedDirectedPosetIndex (C ‘ β) u r).mpr
    ⟨⟨huβ, hrβ⟩, (codedInclusion_directedDefinitions_iff hω he (function_value_mem hC hβ)
      (hchain.binaryUnion_bounded hcarrier) huβ hrβ).mpr ⟨hpos, hdir⟩⟩

theorem firstRubinClause_of_internalChain (hω : HasStandardOmega V) {κ C : V}
    (hκ : IsRegularCardinal κ) (hC : C ∈ boundedBinaryModelCodes κ ^ κ)
    (hchain : IsInternalRelationalChain membershipLanguageCode κ C)
    (hcarrier : codedChainCarrier κ C = κ)
    (hbounds : ∀ β ∈ κ, ∃ c,
      IsCodedCofinalBounds (C ‘ β) (C ‘ (succ β)) (SetTheory.identity (structureDomain (C ‘ β))) c) :
    ∀ P R, IsCodedDefinableSet (codedBinaryChainUnion κ C) P →
      IsCodedDefinableRelation (codedBinaryChainUnion κ C) R →
      IsForcingPoset P R → IsInternalDirectedNoMax P R → ∃ c, IsInternalCofinalStrictChain κ P R c := by
  let : IsOrdinal κ := hκ.1.1
  have hbinary : ∀ β ∈ κ, ∃ D E, C ‘ β = binaryRelationStructureCode D E := by
    intro β hβ
    obtain ⟨D, E, _, _, he⟩ := mem_boundedBinaryModelCodes.mp (function_value_mem hC hβ)
    exact ⟨D, E, he⟩
  have hinc (β : V) (hβ : β ∈ κ) : IsCodedElementaryInclusion (C ‘ β) (codedBinaryChainUnion κ C) :=
    hchain.stage_elementary_binaryUnion_of_binary_stages hbinary hβ
  intro P R hP hR hpos hdir
  obtain ⟨u, hu, huP⟩ := hP.exists_unaryDefinition
  obtain ⟨r, hr, hrR⟩ := hR.exists_binaryDefinition
  obtain ⟨β₀, hβ₀, hindex⟩ := hchain.directedIndex_eventual_stage hω hC hcarrier hu hr
    (by simpa only [huP, hrR] using hpos) (by simpa only [huP, hrR] using hdir)
  apply exists_internalCofinalStrictChain_of_stageBounds hκ hchain hcarrier hβ₀
    (by simpa only [codedBinaryChainUnion, binaryRelationStructureCode_domain, hcarrier] using hP.1)
  intro β hβ hβ₀β
  have hsucc := regularCardinal_succ_closed hκ hβ
  have hi := hindex β hβ hβ₀β
  have hui : u ∈ unaryDefinitionParameters (C ‘ β) := by
    simpa only [kpair.π₁_kpair] using (codedDirectedPosetIndex_spec hi).1
  have hri : r ∈ binaryDefinitionParameters (C ‘ β) := by
    simpa only [kpair.π₂_kpair] using (codedDirectedPosetIndex_spec hi).2.1
  have hβsucc : β ⊆ succ β := mem_subset_refl β
  have hstage : IsCodedElementaryInclusion (C ‘ β) (C ‘ (succ β)) :=
    hchain.elementary β hβ (succ β) hsucc hβsucc
  have hus := unaryDefinitionParameters_mono hstage.subset hui
  have hrs := binaryDefinitionParameters_mono hstage.subset hri
  obtain ⟨c, hc⟩ := hbounds β hβ
  let d := c ‘ ⟨u, r⟩ₖ
  have hd : d ∈ structureDomain (C ‘ (succ β)) := function_value_mem hc.1 hi
  have hdU : d ∈ unaryDefinitionSet (C ‘ (succ β)) u := by
    simpa only [kpair.π₁_kpair, transportDefinition_identity_unary hui] using (hc.2 _ hi).1
  have hdP : d ∈ P := huP ▸ ((hinc (succ β) hsucc).unaryDefinition_iff hus hd).mp hdU
  refine ⟨d, (mem_stageUpperCandidates C P R β d).mpr ⟨hd, hdP, ?_⟩⟩
  intro x hx hxP
  have hxU : x ∈ unaryDefinitionSet (C ‘ β) u :=
    ((hinc β hβ).unaryDefinition_iff hui hx).mpr (huP.symm ▸ hxP)
  have hxdom : x ∈ (codedDirectedPosetDomains (C ‘ β)) ‘ ⟨u, r⟩ₖ := by
    rw [codedDirectedPosetDomains_value hi, kpair.π₁_kpair]
    exact hxU
  have hxR : ⟨x, d⟩ₖ ∈ binaryDefinitionRelation (C ‘ (succ β)) r ∧ x ≠ d := by
    simpa only [kpair.π₂_kpair, transportDefinition_identity_binary hri, identity_value hx] using
      (hc.2 _ hi).2 x hxdom
  exact ⟨hrR ▸ ((hinc (succ β) hsucc).binaryDefinition_iff hrs (hstage.subset x hx) hd).mp hxR.1, hxR.2⟩

theorem internalRubinChain_firstRubinClause (hAC : InternalChoice V) (hω : HasStandardOmega V)
    {A M₀ C : V}
    (hC : C ∈ boundedBinaryModelCodes (hartogsNumber (ω : V)) ^ hartogsNumber (ω : V))
    (hrows : ∀ α ∈ hartogsNumber (ω : V), RubinRow A M₀ α C (C ‘ α)) :
    ∀ P R, IsCodedDefinableSet (codedBinaryChainUnion (hartogsNumber (ω : V)) C) P →
      IsCodedDefinableRelation (codedBinaryChainUnion (hartogsNumber (ω : V)) C) R →
      IsForcingPoset P R → IsInternalDirectedNoMax P R →
      ∃ c, IsInternalCofinalStrictChain (hartogsNumber (ω : V)) P R c :=
  firstRubinClause_of_internalChain hω (hartogsNumber_regular hAC (CardLE.refl _)) hC
    (internalRubinChain_union hC hrows).1 (internalRubinChain_carrier hrows) (internalRubinChain_bounds hrows)

end ZFVP.Schmerl
