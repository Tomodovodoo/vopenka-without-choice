import ZFVP.ModelTheory.MembershipExpansion

/-! Membership structures with an internal set of named elements. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def namedMembershipLanguageCode (I : V) : V :=
  languageCode I (2 : V) (constantGraph I (0 : V)) (constantGraph (2 : V) (2 : V))

instance namedMembershipLanguageCode_definable : ℒₛₑₜ-function₁[V] namedMembershipLanguageCode := by
  unfold namedMembershipLanguageCode
  definability

theorem namedMembershipLanguageCode_valid (I : V) : IsLanguageCode (namedMembershipLanguageCode I) := by
  apply (isLanguageCode_iff _ _ _ _).mpr
  exact ⟨constantGraph_mem_function _ _ _ (by simp), constantGraph_mem_function _ _ _ (by simp)⟩

theorem namedMembershipLanguageCode_extension (I : V) :
    IsMembershipLanguageExtension (namedMembershipLanguageCode I) := by
  refine ⟨namedMembershipLanguageCode_valid I, ?_, ?_⟩
  · simp only [namedMembershipLanguageCode, membershipLanguageCode, relationSymbols_code]
    exact subset_refl _
  · intro r _
    simp only [namedMembershipLanguageCode, membershipLanguageCode, relationArities_code]

noncomputable def namedMembershipFunctions (I A b : V) : V :=
  definableGraph I (fun i ↦ constantGraph (A ^ (0 : V)) (b ‘ i)) (by definability)

instance namedMembershipFunctions_definable : ℒₛₑₜ-function₃[V] namedMembershipFunctions := by
  have hd : ℒₛₑₜ-relation₄[V] (fun F I A b ↦ ∀ p,
      p ∈ F ↔ ∃ i ∈ I, p = ⟨i, constantGraph (A ^ (0 : V)) (b ‘ i)⟩ₖ) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = namedMembershipFunctions (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [namedMembershipFunctions, mem_definableGraph_iff]

noncomputable def namedMembershipStructureCode (I A b : V) : V :=
  structureCode A (namedMembershipFunctions I A b) (structureRelations (membershipStructureCode A))

instance namedMembershipStructureCode_definable : ℒₛₑₜ-function₃[V] namedMembershipStructureCode := by
  unfold namedMembershipStructureCode
  definability

@[simp] theorem namedMembershipStructureCode_domain (I A b : V) :
    structureDomain (namedMembershipStructureCode I A b) = A := structureDomain_code _ _ _

theorem namedMembershipStructureCode_valid {I A b : V} (hA : IsNonempty A) (hb : b ∈ A ^ I) :
    IsStructureCode (namedMembershipLanguageCode I) (namedMembershipStructureCode I A b) := by
  obtain ⟨_, _, _, _, _, hRI, hdom, _, hrel⟩ := membershipStructureCode_valid hA
  simp only [IsStructureCode, namedMembershipStructureCode, namedMembershipLanguageCode,
    structureDomain_code, structureFunctions_code, structureRelations_code,
    functionSymbols_code, relationSymbols_code, functionArities_code, relationArities_code]
  refine ⟨namedMembershipLanguageCode_valid I, True.intro, hA,
    definableGraph_isFunction _ _ _, domain_definableGraph _ _ _, hRI, ?_, ?_, ?_⟩
  · simpa only [membershipLanguageCode, relationSymbols_code] using hdom
  · intro i hi
    rw [namedMembershipFunctions, value_definableGraph _ _ _ hi, value_constantGraph _ _ hi]
    exact constantGraph_mem_function _ _ _ (function_value_mem hb hi)
  · intro r hr
    have hr' : r ∈ relationSymbols (membershipLanguageCode : V) := by
      simpa only [membershipLanguageCode, relationSymbols_code] using hr
    simpa only [membershipStructureCode_domain, membershipLanguageCode, relationArities_code] using hrel r hr'

theorem namedMembershipStructureCode_expansion {I A b : V} (hA : IsNonempty A) (hb : b ∈ A ^ I) :
    IsMembershipExpansion (namedMembershipLanguageCode I) (namedMembershipStructureCode I A b) := by
  refine ⟨namedMembershipLanguageCode_extension I, namedMembershipStructureCode_valid hA hb, ?_⟩
  intro r _
  simp only [namedMembershipStructureCode, structureRelations_code, structureDomain_code]

theorem namedMembershipStructureCode_function_value {I A b i s : V} (hi : i ∈ I)
    (hs : s ∈ A ^ (0 : V)) :
    ((structureFunctions (namedMembershipStructureCode I A b)) ‘ i) ‘ s = b ‘ i := by
  simp only [namedMembershipStructureCode, structureFunctions_code, namedMembershipFunctions]
  rw [value_definableGraph _ _ _ hi, value_constantGraph _ _ hs]

end ZFVP
