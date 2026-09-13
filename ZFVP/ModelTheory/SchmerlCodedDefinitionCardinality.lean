import ZFVP.ModelTheory.SchmerlCodedRubinSource
import ZFVP.ModelTheory.SchmerlInternalCodedSyntaxCountable
import ZFVP.SetTheory.FiniteCardinalArithmetic

/-! Internal bounds for all parametrically definable subsets of a coded model.
Definition codes include every internally finite formula and parameter tuple. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def codedDefinitionCodes (M : V) : V :=
  formulaFamily membershipLanguageCode ∅ ×ˢ finiteSequences (structureDomain M)

def CodedDefinitionInterprets (M d A : V) : Prop := A ⊆ structureDomain M ∧
  ∀ x ∈ structureDomain M, x ∈ A ↔
    codedSatisfies M (kpair.π₁ (kpair.π₁ d)) (kpair.π₂ (kpair.π₁ d))
      (assignmentPrepend (domain (kpair.π₂ d)) (kpair.π₂ d) x)

attribute [local irreducible] codedSatisfies

instance codedDefinitionInterprets_definable : ℒₛₑₜ-relation₃[V] CodedDefinitionInterprets := by
  unfold CodedDefinitionInterprets
  definability

theorem IsCodedDefinableSet.exists_definition_code {M A : V} (h : IsCodedDefinableSet M A) :
    ∃ d ∈ codedDefinitionCodes M, CodedDefinitionInterprets M d A := by
  obtain ⟨hA, n, hn, φ, hφ, b, hb, hdef⟩ := h
  refine ⟨⟨⟨succ n, φ⟩ₖ, b⟩ₖ, ?_, ?_⟩
  · exact kpair_mem_iff.mpr ⟨(mem_formulaSet_iff _ _ _ _).mp hφ,
      (mem_finiteSequences_iff _ _).mpr ⟨n, hn, hb⟩⟩
  · simpa only [CodedDefinitionInterprets, kpair.π₁_kpair, kpair.π₂_kpair, domain_eq_of_mem_function hb] using
      (show A ⊆ structureDomain M ∧ ∀ x ∈ structureDomain M,
        x ∈ A ↔ codedSatisfies M (succ n) φ (assignmentPrepend n b x) from ⟨hA, hdef⟩)

theorem CodedDefinitionInterprets.unique {M d A B : V}
    (hA : CodedDefinitionInterprets M d A) (hB : CodedDefinitionInterprets M d B) : A = B := by
  apply mem_ext
  intro x
  constructor
  · intro hx
    exact (hB.2 x (hA.1 x hx)).mpr ((hA.2 x (hA.1 x hx)).mp hx)
  · intro hx
    exact (hA.2 x (hB.1 x hx)).mpr ((hB.2 x (hB.1 x hx)).mp hx)

noncomputable def codedDefinableSubsets (M : V) : V :=
  {A ∈ ℘ (structureDomain M) ; IsCodedDefinableSet M A}

theorem mem_codedDefinableSubsets (M A : V) :
    A ∈ codedDefinableSubsets M ↔ IsCodedDefinableSet M A := by
  simp only [codedDefinableSubsets, mem_sep_iff, mem_power_iff]
  exact ⟨And.right, fun h ↦ ⟨h.1, h⟩⟩

noncomputable def codedDefinitionCandidates (M A : V) : V :=
  {d ∈ codedDefinitionCodes M ; CodedDefinitionInterprets M d A}

instance codedDefinitionCandidates_definable (M : V) : ℒₛₑₜ-function₁[V] (codedDefinitionCandidates M) := by
  have h : ℒₛₑₜ-relation[V] (fun X A ↦ ∀ d, d ∈ X ↔
      d ∈ codedDefinitionCodes M ∧ CodedDefinitionInterprets M d A) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [codedDefinitionCandidates, mem_sep_iff]
  rfl

theorem codedDefinableSubsets_cardLE_codes (hAC : InternalChoice V) (M : V) :
    codedDefinableSubsets M ≤# codedDefinitionCodes M := by
  obtain ⟨g, hg, hd, hv⟩ := choice_for_definable_family hAC (codedDefinableSubsets M)
    (codedDefinitionCandidates M) inferInstance (by
      intro A hA
      obtain ⟨d, hd, hdef⟩ := ((mem_codedDefinableSubsets M A).mp hA).exists_definition_code
      exact ⟨d, mem_sep_iff.mpr ⟨hd, hdef⟩⟩)
  let : IsFunction g := hg
  have hpair {A d : V} (hAd : ⟨A, d⟩ₖ ∈ g) : d ∈ codedDefinitionCodes M ∧ CodedDefinitionInterprets M d A := by
    have hA := hd ▸ mem_domain_of_kpair_mem hAd
    exact value_eq_of_kpair_mem hAd ▸ mem_sep_iff.mp (hv A hA)
  have hr : range g ⊆ codedDefinitionCodes M := by
    intro d hd
    obtain ⟨A, hAd⟩ := mem_range_iff.mp hd
    exact (hpair hAd).1
  refine ⟨g, ?_, ?_⟩
  · simpa only [hd] using mem_function_of_mem_function_of_subset (IsFunction.mem_function g) hr
  · intro A B d hAd hBd
    exact (hpair hAd).2.unique (hpair hBd).2

theorem codedDefinitionCodes_cardLE (hAC : InternalChoice V) {M lam : V}
    (hlam : IsInitialOrdinal lam) (hω : (ω : V) ⊆ lam) (hM : structureDomain M ≤# lam) :
    codedDefinitionCodes M ≤# lam := by
  have hsyntax : IsInternallyCountable (formulaFamily (membershipLanguageCode : V) ∅) :=
    formulaFamily_countable hAC membershipLanguageCode_valid
      (by simpa only [membershipLanguageCode, functionSymbols_code] using internallyCountable_empty (V := V))
      (by simpa [membershipLanguageCode] using
        internallyCountable_of_finite (internallyFinite_two (V := V))) internallyCountable_empty
  exact prod_cardLE_of_cardLE_initial hlam hω
    (hsyntax.trans (cardLE_of_subset hω)) (finiteSequences_cardLE_of_cardLE_initial hAC hlam hω hM)

theorem codedDefinableSubsets_cardLE (hAC : InternalChoice V) {M lam : V}
    (hlam : IsInitialOrdinal lam) (hω : (ω : V) ⊆ lam) (hM : structureDomain M ≤# lam) :
    codedDefinableSubsets M ≤# lam :=
  (codedDefinableSubsets_cardLE_codes hAC M).trans (codedDefinitionCodes_cardLE hAC hlam hω hM)

end ZFVP.Schmerl
