import ZFVP.ModelTheory.SchmerlInternalFinitaryClosureClub
import ZFVP.ModelTheory.SchmerlCodedDefinitionInclusion
import ZFVP.ModelTheory.InternalNamedSeparationOmission

/-! An actual club reflecting nondefinability to literal coded elementary stages.
The closure operation uses all internal formulas and internally finite parameters. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def rawDefinitionIndices : V :=
  (ω : V) ×ˢ range (formulaFamily membershipLanguageCode ∅)

theorem rawDefinitionIndices_countable (hAC : InternalChoice V) :
    IsInternallyCountable (rawDefinitionIndices : V) := by
  have hs : IsInternallyCountable (formulaFamily (membershipLanguageCode : V) ∅) :=
    formulaFamily_countable hAC membershipLanguageCode_valid
      (by simpa only [membershipLanguageCode, functionSymbols_code] using internallyCountable_empty (V := V))
      (by simpa [membershipLanguageCode] using
        (internallyCountable_subset internallyCountable_omega
          (IsOrdinal.toIsTransitive.transitive (2 : V) (by simp))))
      internallyCountable_empty
  exact (prod_cardLE_prod internallyCountable_omega (internallyCountable_range hs)).trans omega_prod_cardLE_omega

theorem pair_mem_rawDefinitionIndices {n φ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) :
    ⟨n, φ⟩ₖ ∈ (rawDefinitionIndices : V) :=
  kpair_mem_iff.mpr ⟨hn, mem_range_of_kpair_mem ((mem_formulaSet_iff _ _ _ _).mp hφ)⟩

noncomputable def definitionDisagreements (κ N F d : V) : V :=
  {x ∈ κ ; ¬(x ∈ F ↔ x ∈ unaryDefinitionSet N d)}

theorem definitionDisagreements_definable (κ N F : V) :
    ℒₛₑₜ-function₁[V] (definitionDisagreements κ N F) := by
  have hh : ℒₛₑₜ-relation[V] (fun S d ↦ ∀ x,
      x ∈ S ↔ x ∈ κ ∧ ¬(x ∈ F ↔ x ∈ unaryDefinitionSet N d)) := by definability
  apply Language.Definable.of_iff hh
  intro v
  rw [mem_ext_iff]
  simp only [definitionDisagreements, mem_sep_iff]
  rfl

noncomputable def definitionDisagreementWitness (κ N F d : V) : V := by
  classical
  exact if IsNonempty (definitionDisagreements κ N F d) then ⋂ˢ definitionDisagreements κ N F d else 0

theorem definitionDisagreementWitness_definable (κ N F : V) :
    ℒₛₑₜ-function₁[V] (definitionDisagreementWitness κ N F) := by
  have := definitionDisagreements_definable κ N F
  have hh : ℒₛₑₜ-relation[V] (fun x d ↦
      (IsNonempty (definitionDisagreements κ N F d) ∧ x = ⋂ˢ definitionDisagreements κ N F d) ∨
      (¬IsNonempty (definitionDisagreements κ N F d) ∧ x = 0)) := by definability
  apply Language.Definable.of_iff hh
  intro v
  simp only [definitionDisagreementWitness]
  split_ifs <;> simp_all

theorem definitionDisagreementWitness_mem {κ N F d : V} [IsOrdinal κ] (hzero : (0 : V) ∈ κ) :
    definitionDisagreementWitness κ N F d ∈ κ := by
  classical
  unfold definitionDisagreementWitness
  split_ifs with h
  · have := h
    exact (mem_sep_iff.mp (IsOrdinal.sInter_mem (X := definitionDisagreements κ N F d)
      (fun x hx ↦ IsOrdinal.of_mem (mem_sep_iff.mp hx).1))).1
  · exact hzero

theorem definitionDisagreementWitness_spec {κ N F d : V} [IsOrdinal κ]
    (hN : structureDomain N = κ) (hF : F ⊆ κ) (hnot : ¬IsCodedDefinableSet N F)
    (hd : d ∈ unaryDefinitionParameters N) :
    definitionDisagreementWitness κ N F d ∈ κ ∧
      ¬(definitionDisagreementWitness κ N F d ∈ F ↔
        definitionDisagreementWitness κ N F d ∈ unaryDefinitionSet N d) := by
  classical
  have hne : IsNonempty (definitionDisagreements κ N F d) := by
    have hex : ∃ x ∈ κ, ¬(x ∈ F ↔ x ∈ unaryDefinitionSet N d) := by
      by_contra h
      push Not at h
      have he : unaryDefinitionSet N d = F := by
        ext x
        constructor
        · intro hx
          exact (h x (hN ▸ unaryDefinitionSet_subset N d x hx)).mpr hx
        · intro hx
          exact (h x (hF x hx)).mp hx
      exact hnot (he ▸ unaryDefinitionSet_isCodedDefinable hd)
    obtain ⟨x, hx, hb⟩ := hex
    exact ⟨x, mem_sep_iff.mpr ⟨hx, hb⟩⟩
  have hw := IsOrdinal.sInter_mem (X := definitionDisagreements κ N F d)
    (fun x hx ↦ IsOrdinal.of_mem (mem_sep_iff.mp hx).1)
  simpa only [definitionDisagreementWitness, ite_eq_left hne] using (mem_sep_iff.mp hw)

noncomputable def definitionDisagreementGraph (κ N F : V) : V :=
  definableGraph ((rawDefinitionIndices : V) ×ˢ finiteSequences κ)
    (definitionDisagreementWitness κ N F) (definitionDisagreementWitness_definable κ N F)

theorem definitionDisagreementGraph_mem {κ N F : V} [IsOrdinal κ] (hzero : (0 : V) ∈ κ) :
    definitionDisagreementGraph κ N F ∈ κ ^ ((rawDefinitionIndices : V) ×ˢ finiteSequences κ) :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ _ ↦ definitionDisagreementWitness_mem hzero)

theorem definitionDisagreementGraph_value {κ N F n φ b : V}
    (hn : n ∈ (ω : V)) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n))
    (hb : b ∈ finiteSequences κ) :
    (definitionDisagreementGraph κ N F) ‘ ⟨⟨n, φ⟩ₖ, b⟩ₖ =
      definitionDisagreementWitness κ N F ⟨⟨n, φ⟩ₖ, b⟩ₖ :=
  value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨pair_mem_rawDefinitionIndices hn hφ, hb⟩)

/-- A stage closed under actual disagreement witnesses cannot separate its two traces. -/
theorem codedInseparable_of_disagreement_closed {κ N M F : V} [IsOrdinal κ]
    (hN : structureDomain N = κ) (hF : F ⊆ κ) (hnot : ¬IsCodedDefinableSet N F)
    (hMN : IsCodedElementaryInclusion M N)
    (hclosed : ∀ d ∈ unaryDefinitionParameters M,
      definitionDisagreementWitness κ N F d ∈ structureDomain M) :
    IsCodedInseparable M (F ∩ structureDomain M) (structureDomain M \ F) := by
  classical
  refine ⟨fun _ hx ↦ (mem_inter_iff.mp hx).2, fun _ hx ↦ (mem_sdiff_iff.mp hx).1, ?_⟩
  rintro ⟨X, hX, hUX, hWX⟩
  obtain ⟨d, hd, he⟩ := hX.exists_unaryDefinition
  let x := definitionDisagreementWitness κ N F d
  have hxM : x ∈ structureDomain M := hclosed d hd
  have hdN := unaryDefinitionParameters_mono hMN.subset hd
  have hx := definitionDisagreementWitness_spec hN hF hnot hdN
  apply hx.2
  have hxe : x ∈ unaryDefinitionSet N d ↔ x ∈ X := by
    rw [← he]
    exact (hMN.unaryDefinition_iff hd hxM).symm
  rw [hxe]
  constructor
  · intro hxF
    exact hUX x (mem_inter_iff.mpr ⟨hxF, hxM⟩)
  · intro hxX
    by_contra hxF
    exact hWX x (mem_sdiff_iff.mpr ⟨hxM, hxF⟩) hxX

/-- Carrier agreement may be supplied after intersecting this club with other clubs. -/
theorem exists_hartogsOmega_nondefinabilityClub (hAC : InternalChoice V) {N C F : V}
    (hN : structureDomain N = hartogsNumber (ω : V)) (hF : F ⊆ hartogsNumber (ω : V))
    (hnot : ¬IsCodedDefinableSet N F)
    (hC : ∀ α ∈ hartogsNumber (ω : V), IsCodedElementaryInclusion (C ‘ α) N) :
    ∃ E : V, IsClubIn E (hartogsNumber (ω : V)) ∧ ∀ α ∈ E,
      structureDomain (C ‘ α) = α → IsCodedInseparable (C ‘ α) (F ∩ α) (α \ F) := by
  let κ := hartogsNumber (ω : V)
  have hzero : (0 : V) ∈ κ := IsOrdinal.toIsTransitive.mem_trans empty_mem_ω omega_mem_hartogs_omega
  have hg := definitionDisagreementGraph_mem (N := N) (F := F) hzero
  have hI := rawDefinitionIndices_countable (V := V) hAC
  let E := finitaryClosureClub κ (rawDefinitionIndices : V) (definitionDisagreementGraph κ N F)
  have hE : IsClubIn E κ := hartogsOmega_finitaryClosureClub hAC hI hg
  refine ⟨E, hE, fun α hα hD ↦ ?_⟩
  have hακ := hE.1.1 α hα
  have hclosure := (hartogsOmega_finitaryClosureClub_closed hAC hI hg hα).2
  have hsep := codedInseparable_of_disagreement_closed hN hF hnot (hC α hακ) ?_
  · simpa only [hD] using hsep
  intro d hd
  obtain ⟨n, hn, φ, hφ, b, hb, rfl⟩ := unaryDefinitionParameters_cases hd
  have hbα : b ∈ finiteSequences α := (mem_finiteSequences_iff _ _).mpr ⟨n, hn, hD ▸ hb⟩
  have hbκ : b ∈ finiteSequences κ := (mem_finiteSequences_iff _ _).mpr
    ⟨n, hn, mem_function_of_mem_function_of_subset (hD ▸ hb) (IsTransitive.transitive α hακ)⟩
  rw [hD, ← definitionDisagreementGraph_value (N := N) (F := F) hn hφ hbκ]
  exact hclosure _ (pair_mem_rawDefinitionIndices hn hφ) b hbα

end ZFVP.Schmerl
