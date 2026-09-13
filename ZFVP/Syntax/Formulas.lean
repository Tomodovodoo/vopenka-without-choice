import ZFVP.Syntax.FormulaCodes

/-! The least internal family of formulas in all finite bound-variable contexts. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

attribute [local aesop 4 (rule_sets := [Definability]) safe]
  Language.DefinableRel₅.comp

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Members are context/formula pairs. Quantifier bodies have one more bound variable. -/
def IsFormulaClosed (L Γ Q : V) : Prop := ∀ n ∈ (ω : V),
  (⟨n, truthCode⟩ₖ ∈ Q ∧ ⟨n, falsityCode⟩ₖ ∈ Q) ∧
  (∀ r args, IsAtomicArguments L Γ n r args →
    ⟨n, atomCode r args⟩ₖ ∈ Q ∧ ⟨n, negAtomCode r args⟩ₖ ∈ Q) ∧
  (∀ φ ψ, ⟨n, φ⟩ₖ ∈ Q → ⟨n, ψ⟩ₖ ∈ Q →
    ⟨n, andCode φ ψ⟩ₖ ∈ Q ∧ ⟨n, orCode φ ψ⟩ₖ ∈ Q) ∧
  ∀ φ, ⟨succ n, φ⟩ₖ ∈ Q → ⟨n, allCode φ⟩ₖ ∈ Q ∧ ⟨n, existsCode φ⟩ₖ ∈ Q

instance isFormulaClosed_definable : ℒₛₑₜ-relation₃[V] IsFormulaClosed := by
  unfold IsFormulaClosed truthCode falsityCode
  definability

noncomputable def formulaFamily (L Γ : V) : V :=
  {p ∈ syntaxUniverse L Γ ; ∀ Q, IsFormulaClosed L Γ Q → p ∈ Q}

theorem mem_formulaFamily_iff (L Γ p : V) : p ∈ formulaFamily L Γ ↔
    p ∈ syntaxUniverse L Γ ∧ ∀ Q, IsFormulaClosed L Γ Q → p ∈ Q := by simp [formulaFamily]

instance formulaFamily_definable : ℒₛₑₜ-function₂[V] formulaFamily := by
  have h : ℒₛₑₜ-relation₃ (fun F L Γ : V ↦ ∀ p, p ∈ F ↔
      p ∈ syntaxUniverse L Γ ∧ ∀ Q, IsFormulaClosed L Γ Q → p ∈ Q) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = formulaFamily (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_formulaFamily_iff]

theorem formulaFamily_minimal {L Γ Q : V} (hQ : IsFormulaClosed L Γ Q) : formulaFamily L Γ ⊆ Q :=
  fun p hp ↦ ((mem_formulaFamily_iff L Γ p).mp hp).2 Q hQ

theorem formulaFamily_subset_syntaxUniverse (L Γ : V) : formulaFamily L Γ ⊆ syntaxUniverse L Γ :=
  fun p hp ↦ ((mem_formulaFamily_iff L Γ p).mp hp).1

theorem syntaxUniverse_formulaClosed {L : V} (hL : IsLanguageCode L) (Γ : V) :
    IsFormulaClosed L Γ (syntaxUniverse L Γ) := by
  intro n hn
  have hnU : n ∈ syntaxUniverse L Γ := codingUniverse_natural_mem _ hn
  refine ⟨⟨codingUniverse_kpair_closed hnU (truthCode_mem_syntaxUniverse L Γ),
    codingUniverse_kpair_closed hnU (falsityCode_mem_syntaxUniverse L Γ)⟩, ?_, ?_, ?_⟩
  · intro r args ha
    obtain ⟨hp, hn⟩ := atomCodes_mem_syntaxUniverse hL hn ha
    exact ⟨codingUniverse_kpair_closed hnU hp, codingUniverse_kpair_closed hnU hn⟩
  · intro φ ψ hφ hψ
    obtain ⟨ha, ho⟩ := binaryCodes_mem_syntaxUniverse
      (kpair_components_mem_transitive hφ).2 (kpair_components_mem_transitive hψ).2
    exact ⟨codingUniverse_kpair_closed hnU ha, codingUniverse_kpair_closed hnU ho⟩
  · intro φ hφ
    obtain ⟨ha, he⟩ := quantifierCodes_mem_syntaxUniverse (kpair_components_mem_transitive hφ).2
    exact ⟨codingUniverse_kpair_closed hnU ha, codingUniverse_kpair_closed hnU he⟩

theorem formulaFamily_closed {L : V} (hL : IsLanguageCode L) (Γ : V) :
    IsFormulaClosed L Γ (formulaFamily L Γ) := by
  intro n hn
  have hU := syntaxUniverse_formulaClosed hL Γ n hn
  have hsub := formulaFamily_subset_syntaxUniverse L Γ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨(mem_formulaFamily_iff _ _ _).mpr ⟨hU.1.1, fun Q hQ ↦ (hQ n hn).1.1⟩,
      (mem_formulaFamily_iff _ _ _).mpr ⟨hU.1.2, fun Q hQ ↦ (hQ n hn).1.2⟩⟩
  · intro r args ha
    exact ⟨(mem_formulaFamily_iff _ _ _).mpr
        ⟨(hU.2.1 r args ha).1, fun Q hQ ↦ ((hQ n hn).2.1 r args ha).1⟩,
      (mem_formulaFamily_iff _ _ _).mpr
        ⟨(hU.2.1 r args ha).2, fun Q hQ ↦ ((hQ n hn).2.1 r args ha).2⟩⟩
  · intro φ ψ hφ hψ
    have hu := hU.2.2.1 φ ψ (hsub _ hφ) (hsub _ hψ)
    have hq : ∀ Q, IsFormulaClosed L Γ Q →
        ⟨n, andCode φ ψ⟩ₖ ∈ Q ∧ ⟨n, orCode φ ψ⟩ₖ ∈ Q := by
      intro Q hQ
      exact (hQ n hn).2.2.1 φ ψ (formulaFamily_minimal hQ _ hφ) (formulaFamily_minimal hQ _ hψ)
    exact ⟨(mem_formulaFamily_iff _ _ _).mpr ⟨hu.1, fun Q hQ ↦ (hq Q hQ).1⟩,
      (mem_formulaFamily_iff _ _ _).mpr ⟨hu.2, fun Q hQ ↦ (hq Q hQ).2⟩⟩
  · intro φ hφ
    have hu := hU.2.2.2 φ (hsub _ hφ)
    have hq : ∀ Q, IsFormulaClosed L Γ Q →
        ⟨n, allCode φ⟩ₖ ∈ Q ∧ ⟨n, existsCode φ⟩ₖ ∈ Q := by
      intro Q hQ
      exact (hQ n hn).2.2.2 φ (formulaFamily_minimal hQ _ hφ)
    exact ⟨(mem_formulaFamily_iff _ _ _).mpr ⟨hu.1, fun Q hQ ↦ (hq Q hQ).1⟩,
      (mem_formulaFamily_iff _ _ _).mpr ⟨hu.2, fun Q hQ ↦ (hq Q hQ).2⟩⟩

noncomputable def formulaSet (L Γ n : V) : V :=
  {φ ∈ syntaxUniverse L Γ ; ⟨n, φ⟩ₖ ∈ formulaFamily L Γ}

theorem mem_formulaSet_iff (L Γ n φ : V) :
    φ ∈ formulaSet L Γ n ↔ ⟨n, φ⟩ₖ ∈ formulaFamily L Γ := by
  simp only [formulaSet, mem_sep_iff, and_iff_right_iff_imp]
  intro h
  exact (kpair_components_mem_transitive (formulaFamily_subset_syntaxUniverse L Γ _ h)).2

instance formulaSet_definable : ℒₛₑₜ-function₃[V] formulaSet := by
  have h : ℒₛₑₜ-relation₄ (fun F L Γ n : V ↦ ∀ φ, φ ∈ F ↔ ⟨n, φ⟩ₖ ∈ formulaFamily L Γ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = formulaSet (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [mem_formulaSet_iff]

end ZFVP
