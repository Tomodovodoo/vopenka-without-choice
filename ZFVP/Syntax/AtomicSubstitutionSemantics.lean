import ZFVP.Syntax.TermSubstitutionSemantics
import ZFVP.Syntax.AtomicSatisfaction

/-! Equality and relation atoms respect internal simultaneous substitution. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem evaluatedArguments_substitution {L Γ Δ n m M B E b e args a : V}
    (hM : IsStructureCode L M) (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hB : B ∈ termSet L Δ m ^ n) (hE : E ∈ termSet L Δ m ^ Γ)
    (hb : b ∈ structureDomain M ^ m) (he : e ∈ structureDomain M ^ Δ)
    (ha : args ∈ termSet L Γ n ^ a) :
    evaluatedArguments L Δ M e m b (compose args (termSubstitution L Γ n B E)) =
      evaluatedArguments L Γ M (compose E (termEvaluation L Δ m M b e)) n
        (compose B (termEvaluation L Δ m M b e)) args := by
  have hT := termEvaluation_mem_function hM hm Δ hb he
  have hS := termSubstitution_mem_function hM.language hn hm hB hE
  have hU := termEvaluation_mem_function hM hn Γ (compose_function hB hT) (compose_function hE hT)
  apply function_eq_of_values (compose_function (compose_function ha hS) hT) (compose_function ha hU)
  intro i hi
  rw [value_compose_of_mem_function (compose_function ha hS) hT hi,
    value_compose_of_mem_function ha hS hi]
  rw [value_compose_of_mem_function ha hU hi]
  exact termEvaluation_substitution hM hn hm hB hE hb he _ (function_value_mem ha hi)

theorem atomicHolds_substitution {L Γ Δ n m M B E b e r args : V}
    (hM : IsStructureCode L M) (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hB : B ∈ termSet L Δ m ^ n) (hE : E ∈ termSet L Δ m ^ Γ)
    (hb : b ∈ structureDomain M ^ m) (he : e ∈ structureDomain M ^ Δ)
    (ha : IsAtomicArguments L Γ n r args) :
    AtomicHolds L Δ M e m b r (compose args (termSubstitution L Γ n B E)) ↔
      AtomicHolds L Γ M (compose E (termEvaluation L Δ m M b e)) n
        (compose B (termEvaluation L Δ m M b e)) r args := by
  have hargs : evaluatedArguments L Δ M e m b (compose args (termSubstitution L Γ n B E)) =
      evaluatedArguments L Γ M (compose E (termEvaluation L Δ m M b e)) n
        (compose B (termEvaluation L Δ m M b e)) args := by
    rcases ha with ⟨_, ha⟩ | ⟨s, _, _, ha⟩
    · exact evaluatedArguments_substitution hM hn hm hB hE hb he ha
    · exact evaluatedArguments_substitution hM hn hm hB hE hb he ha
  unfold AtomicHolds
  rw [hargs]

end ZFVP
