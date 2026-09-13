import ZFVP.Syntax.FormulaInduction

/-! Every internal formula is produced by one of the eight constructors. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

attribute [local aesop 4 (rule_sets := [Definability]) safe]
  Language.DefinableRel₅.comp

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsFormulaConstructor (L Γ n φ : V) : Prop :=
  φ = truthCode ∨ φ = falsityCode ∨
  (∃ r args, IsAtomicArguments L Γ n r args ∧ (φ = atomCode r args ∨ φ = negAtomCode r args)) ∨
  (∃ ψ χ, ψ ∈ formulaSet L Γ n ∧ χ ∈ formulaSet L Γ n ∧
    (φ = andCode ψ χ ∨ φ = orCode ψ χ)) ∨
  ∃ ψ, ψ ∈ formulaSet L Γ (succ n) ∧ (φ = allCode ψ ∨ φ = existsCode ψ)

instance isFormulaConstructor_definable : ℒₛₑₜ-relation₄[V] IsFormulaConstructor := by
  unfold IsFormulaConstructor truthCode falsityCode
  definability

theorem formulaSet_cases {L Γ n φ : V} (hL : IsLanguageCode L)
    (hφ : φ ∈ formulaSet L Γ n) : IsFormulaConstructor L Γ n φ := by
  apply formulaSet_induction hL Γ (IsFormulaConstructor L Γ) (by definability) ?_ ?_ ?_ ?_ n φ hφ
  · intro n hn
    exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩
  · intro n hn r args ha
    exact ⟨Or.inr (Or.inr (Or.inl ⟨r, args, ha, Or.inl rfl⟩)),
      Or.inr (Or.inr (Or.inl ⟨r, args, ha, Or.inr rfl⟩))⟩
  · intro n hn ψ χ hψ hχ _ _
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨ψ, χ, hψ, hχ, Or.inl rfl⟩))),
      Or.inr (Or.inr (Or.inr (Or.inl ⟨ψ, χ, hψ, hχ, Or.inr rfl⟩)))⟩
  · intro n hn ψ hψ _
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨ψ, hψ, Or.inl rfl⟩))),
      Or.inr (Or.inr (Or.inr (Or.inr ⟨ψ, hψ, Or.inr rfl⟩)))⟩

theorem mem_formulaSet_iff_constructor {L Γ n φ : V} (hL : IsLanguageCode L) :
    φ ∈ formulaSet L Γ n ↔ n ∈ (ω : V) ∧ IsFormulaConstructor L Γ n φ := by
  constructor
  · intro hφ
    exact ⟨formulaSet_context hL hφ, formulaSet_cases hL hφ⟩
  · rintro ⟨hn, hφ⟩
    rcases hφ with rfl | rfl | ⟨r, args, ha, heq⟩ | ⟨ψ, χ, hψ, hχ, heq⟩ | ⟨ψ, hψ, heq⟩
    · exact (formulaSet_constants hL hn Γ).1
    · exact (formulaSet_constants hL hn Γ).2
    · rcases heq with rfl | rfl
      · exact (formulaSet_atoms hL hn ha).1
      · exact (formulaSet_atoms hL hn ha).2
    · rcases heq with rfl | rfl
      · exact (formulaSet_binary hL hn hψ hχ).1
      · exact (formulaSet_binary hL hn hψ hχ).2
    · rcases heq with rfl | rfl
      · exact (formulaSet_quantifiers hL hn hψ).1
      · exact (formulaSet_quantifiers hL hn hψ).2

end ZFVP
