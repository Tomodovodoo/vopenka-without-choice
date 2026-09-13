import ZFVP.Syntax.UniformSatisfaction
import ZFVP.SetTheory.FiniteSets

/-! Finite conjunctions for actual internally finite sets of raw formulas. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

theorem exists_internal_finiteConjunction {L Γ n A : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hA : IsInternallyFinite A) (hsub : A ⊆ formulaSet L Γ n) :
    ∃ χ ∈ formulaSet L Γ n, ∀ M e b, b ∈ structureDomain M ^ n →
      (Satisfies L Γ M e n χ b ↔ ∀ φ ∈ A, Satisfies L Γ M e n φ b) := by
  let : ℒₛₑₜ-function₄[V] satisfactionGraph := satisfactionGraphFormula_defined.to_definable
  have H : ∀ A, IsInternallyFinite A → A ⊆ formulaSet L Γ n →
      ∃ χ ∈ formulaSet L Γ n, ∀ M e b, b ∈ structureDomain M ^ n →
        (Satisfies L Γ M e n χ b ↔ ∀ φ ∈ A, Satisfies L Γ M e n φ b) := by
    apply internallyFinite_induction
      (fun A ↦ A ⊆ formulaSet L Γ n → ∃ χ ∈ formulaSet L Γ n,
        ∀ M e b, b ∈ structureDomain M ^ n →
          (Satisfies L Γ M e n χ b ↔ ∀ φ ∈ A, Satisfies L Γ M e n φ b))
      (by unfold Satisfies; definability)
    · intro _
      refine ⟨truthCode, (formulaSet_constants hL hn Γ).1, ?_⟩
      intro M e b hb
      rw [satisfies_truth hL hn]
      simp only [not_mem_empty, false_implies, implies_true, iff_true]
      exact hb
    · intro A φ ih hsub
      have hφ : φ ∈ formulaSet L Γ n := hsub φ (by simp)
      obtain ⟨χ, hχ, heq⟩ := ih (fun ψ hψ ↦ hsub ψ (mem_insert.mpr (Or.inr hψ)))
      refine ⟨andCode φ χ, (formulaSet_binary hL hn hφ hχ).1, ?_⟩
      intro M e b hb
      rw [satisfies_and hL hn hφ hχ hb, heq M e b hb]
      simp only [mem_insert]
      constructor
      · rintro ⟨hφ, hA⟩ ψ (rfl | hψ)
        · exact hφ
        · exact hA ψ hψ
      · intro hh
        exact ⟨hh φ (Or.inl rfl), fun ψ hψ ↦ hh ψ (Or.inr hψ)⟩
  exact H A hA hsub

end ZFVP
