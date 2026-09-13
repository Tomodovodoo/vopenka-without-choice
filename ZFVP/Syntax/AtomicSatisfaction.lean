import ZFVP.Syntax.Atoms

/-! Satisfaction of logical equality and relation atoms using internal term evaluation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def evaluateWithFreeAssignment (L Γ M e n b : V) : V := termEvaluation L Γ n M b e

instance termEvaluation_fixed_definable (L Γ M e : V) :
    ℒₛₑₜ-function₂ (evaluateWithFreeAssignment L Γ M e) := by
  exact Language.DefinableFunction.substitution
    (f := ![fun _ ↦ L, fun _ ↦ Γ, fun v : Fin 2 → V ↦ v 0,
      fun _ ↦ M, fun v ↦ v 1, fun _ ↦ e]) termEvaluation_definable
    (by
      simp only [Fin.forall_fin_iff_zero_and_forall_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.forall_fin_zero, and_true]
      exact ⟨by definability, by definability, by definability, by definability, by definability, by definability⟩)

noncomputable def evaluatedArguments (L Γ M e n b args : V) : V :=
  compose args (evaluateWithFreeAssignment L Γ M e n b)

instance evaluatedArguments_definable (L Γ M e : V) :
    ℒₛₑₜ-function₃ (evaluatedArguments L Γ M e) := by
  unfold evaluatedArguments
  definability

def AtomicHolds (L Γ M e n b r args : V) : Prop :=
  (r = equalityToken ∧ (evaluatedArguments L Γ M e n b args) ‘ (0 : V) =
    (evaluatedArguments L Γ M e n b args) ‘ (1 : V)) ∨
  ∃ s ∈ relationSymbols L, r = relationToken s ∧
    evaluatedArguments L Γ M e n b args ∈ (structureRelations M) ‘ s

instance atomicHolds_definable (L Γ M e : V) : ℒₛₑₜ-relation₄ (AtomicHolds L Γ M e) := by
  unfold AtomicHolds equalityToken
  definability

theorem atomicHolds_equality (L Γ M e n b args : V) :
    AtomicHolds L Γ M e n b equalityToken args ↔
      (evaluatedArguments L Γ M e n b args) ‘ (0 : V) =
        (evaluatedArguments L Γ M e n b args) ‘ (1 : V) := by
  simp [AtomicHolds]

theorem atomicHolds_relation (L Γ M e n b s args : V) :
    AtomicHolds L Γ M e n b (relationToken s) args ↔ s ∈ relationSymbols L ∧
      evaluatedArguments L Γ M e n b args ∈ (structureRelations M) ‘ s := by
  have hne := (equalityToken_ne_relationToken (V := V) s).symm
  simp [AtomicHolds, hne]

theorem evaluatedArguments_mem_function {L Γ M e n b args k : V}
    (hM : IsStructureCode L M) (hn : n ∈ (ω : V))
    (hb : b ∈ structureDomain M ^ n) (he : e ∈ structureDomain M ^ Γ)
    (ha : args ∈ termSet L Γ n ^ k) :
    evaluatedArguments L Γ M e n b args ∈ structureDomain M ^ k :=
  compose_function ha (termEvaluation_mem_function hM hn Γ hb he)

end ZFVP

