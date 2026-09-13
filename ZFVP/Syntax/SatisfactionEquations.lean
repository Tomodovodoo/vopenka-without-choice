import ZFVP.Syntax.SatisfactionStepEquations

/-! The eight semantic clauses for valid internal formulas and bound assignments. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem satisfaction_previous_value {L Γ M e s t : V} (hL : IsLanguageCode L)
    (ht : t ∈ formulaFamily L Γ) (hst : IsImmediateSubformula s t) :
    ((satisfactionGraph L Γ M e) ↾
      (predecessors (subformulaRelation (formulaFamily L Γ)) (formulaFamily L Γ) t)) ‘ s =
      (satisfactionGraph L Γ M e) ‘ s :=
  formulaRecursion_previous_value hL _ _ ht hst

theorem satisfies_truth {L Γ M e n b : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V)) :
    Satisfies L Γ M e n truthCode b ↔ b ∈ structureDomain M ^ n := by
  rw [satisfies_iff_step (formulaSet_constants hL hn Γ).1, satisfactionStepHolds_truth]
  simp

theorem not_satisfies_falsity {L Γ M e n b : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V)) :
    ¬Satisfies L Γ M e n falsityCode b := by
  rw [satisfies_iff_step (formulaSet_constants hL hn Γ).2, satisfactionStepHolds_falsity]
  simp

theorem satisfies_atom {L Γ M e n b r args : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments L Γ n r args) (hb : b ∈ structureDomain M ^ n) :
    Satisfies L Γ M e n (atomCode r args) b ↔ AtomicHolds L Γ M e n b r args := by
  rw [satisfies_iff_step (formulaSet_atoms hL hn ha).1, satisfactionStepHolds_atom]
  exact and_iff_right hb

theorem satisfies_negAtom {L Γ M e n b r args : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments L Γ n r args) (hb : b ∈ structureDomain M ^ n) :
    Satisfies L Γ M e n (negAtomCode r args) b ↔ ¬AtomicHolds L Γ M e n b r args := by
  rw [satisfies_iff_step (formulaSet_atoms hL hn ha).2, satisfactionStepHolds_negAtom]
  exact and_iff_right hb

theorem satisfies_and {L Γ M e n b φ ψ : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet L Γ n) (hψ : ψ ∈ formulaSet L Γ n) (hb : b ∈ structureDomain M ^ n) :
    Satisfies L Γ M e n (andCode φ ψ) b ↔ Satisfies L Γ M e n φ b ∧ Satisfies L Γ M e n ψ b := by
  have hp := (formulaSet_binary hL hn hφ hψ).1
  have hpf := (mem_formulaSet_iff _ _ _ _).mp hp
  have hsφ : IsImmediateSubformula ⟨n, φ⟩ₖ ⟨n, andCode φ ψ⟩ₖ :=
    Or.inl ⟨n, φ, ψ, Or.inl rfl, Or.inl rfl⟩
  have hsψ : IsImmediateSubformula ⟨n, ψ⟩ₖ ⟨n, andCode φ ψ⟩ₖ :=
    Or.inl ⟨n, φ, ψ, Or.inl rfl, Or.inr rfl⟩
  rw [satisfies_iff_step hp, satisfactionStepHolds_and,
    satisfaction_previous_value hL hpf hsφ, satisfaction_previous_value hL hpf hsψ]
  exact and_iff_right hb

theorem satisfies_or {L Γ M e n b φ ψ : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet L Γ n) (hψ : ψ ∈ formulaSet L Γ n) (hb : b ∈ structureDomain M ^ n) :
    Satisfies L Γ M e n (orCode φ ψ) b ↔ Satisfies L Γ M e n φ b ∨ Satisfies L Γ M e n ψ b := by
  have hp := (formulaSet_binary hL hn hφ hψ).2
  have hpf := (mem_formulaSet_iff _ _ _ _).mp hp
  have hsφ : IsImmediateSubformula ⟨n, φ⟩ₖ ⟨n, orCode φ ψ⟩ₖ :=
    Or.inl ⟨n, φ, ψ, Or.inr rfl, Or.inl rfl⟩
  have hsψ : IsImmediateSubformula ⟨n, ψ⟩ₖ ⟨n, orCode φ ψ⟩ₖ :=
    Or.inl ⟨n, φ, ψ, Or.inr rfl, Or.inr rfl⟩
  rw [satisfies_iff_step hp, satisfactionStepHolds_or,
    satisfaction_previous_value hL hpf hsφ, satisfaction_previous_value hL hpf hsψ]
  exact and_iff_right hb

theorem satisfies_all {L Γ M e n b φ : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet L Γ (succ n)) (hb : b ∈ structureDomain M ^ n) :
    Satisfies L Γ M e n (allCode φ) b ↔
      ∀ x ∈ structureDomain M, Satisfies L Γ M e (succ n) φ (assignmentPrepend n b x) := by
  have hp := (formulaSet_quantifiers hL hn hφ).1
  have hpf := (mem_formulaSet_iff _ _ _ _).mp hp
  have hs : IsImmediateSubformula ⟨succ n, φ⟩ₖ ⟨n, allCode φ⟩ₖ :=
    Or.inr ⟨n, φ, Or.inl rfl, rfl⟩
  rw [satisfies_iff_step hp, satisfactionStepHolds_all, satisfaction_previous_value hL hpf hs]
  exact and_iff_right hb

theorem satisfies_exists {L Γ M e n b φ : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet L Γ (succ n)) (hb : b ∈ structureDomain M ^ n) :
    Satisfies L Γ M e n (existsCode φ) b ↔
      ∃ x ∈ structureDomain M, Satisfies L Γ M e (succ n) φ (assignmentPrepend n b x) := by
  have hp := (formulaSet_quantifiers hL hn hφ).2
  have hpf := (mem_formulaSet_iff _ _ _ _).mp hp
  have hs : IsImmediateSubformula ⟨succ n, φ⟩ₖ ⟨n, existsCode φ⟩ₖ :=
    Or.inr ⟨n, φ, Or.inr rfl, rfl⟩
  rw [satisfies_iff_step hp, satisfactionStepHolds_exists, satisfaction_previous_value hL hpf hs]
  exact and_iff_right hb

end ZFVP

