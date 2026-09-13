import ZFVP.Syntax.TermRecursion
import ZFVP.SetTheory.FunctionComposition
import ZFVP.ModelTheory.StructureCode

/-! Evaluation of internal terms in a coded structure with set-coded assignments. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

attribute [local aesop 4 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₅.comp

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def termEvaluationStep (M b e t previous : V) : V := by
  classical
  exact
  if kpair.π₁ t = 0 then b ‘ (kpair.π₂ t)
  else if kpair.π₁ t = 1 then e ‘ (kpair.π₂ t)
  else ((structureFunctions M) ‘ (kpair.π₁ (kpair.π₂ t))) ‘
    (compose (kpair.π₂ (kpair.π₂ t)) previous)

instance termEvaluationStep_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (termEvaluationStep (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun z M b e t previous : V ↦
      (kpair.π₁ t = 0 ∧ z = b ‘ (kpair.π₂ t)) ∨
      (kpair.π₁ t ≠ 0 ∧ kpair.π₁ t = 1 ∧ z = e ‘ (kpair.π₂ t)) ∨
      (kpair.π₁ t ≠ 0 ∧ kpair.π₁ t ≠ 1 ∧ z =
        ((structureFunctions M) ‘ (kpair.π₁ (kpair.π₂ t))) ‘
          (compose (kpair.π₂ (kpair.π₂ t)) previous))) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = termEvaluationStep (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  unfold termEvaluationStep
  split <;> simp_all
  split <;> simp_all

instance termEvaluationStep_structure_definable (M : V) :
    ℒₛₑₜ-function₄ (termEvaluationStep M) := by
  exact Language.DefinableFunction₅.comp (by definability) (by definability)
    (by definability) (by definability) (by definability)

@[simp] theorem termEvaluationStep_boundVar (M b e i previous : V) :
    termEvaluationStep M b e (boundVarCode i) previous = b ‘ i := by
  simp [termEvaluationStep, boundVarCode]

@[simp] theorem termEvaluationStep_freeVar (M b e x previous : V) :
    termEvaluationStep M b e (freeVarCode x) previous = e ‘ x := by
  simp [termEvaluationStep, freeVarCode]

@[simp] theorem termEvaluationStep_function (M b e f args previous : V) :
    termEvaluationStep M b e (functionTermCode f args) previous =
      ((structureFunctions M) ‘ f) ‘ (compose args previous) := by
  have h20 : (2 : V) ≠ 0 := by
    intro h
    have := (natCast_eq_iff (V := V) 2 0).mp h
    contradiction
  have h21 : (2 : V) ≠ 1 := by
    intro h
    have := (natCast_eq_iff (V := V) 2 1).mp h
    contradiction
  simp [termEvaluationStep, functionTermCode, h20, h21]

noncomputable def termEvaluation (L Γ n M b e : V) : V :=
  termRecursion L Γ n (termEvaluationStep M b e) (by definability)

instance termEvaluation_isFunction (L Γ n M b e : V) :
    IsFunction (termEvaluation L Γ n M b e) := termRecursion_isFunction _ _ _ _ _

@[simp] theorem domain_termEvaluation (L Γ n M b e : V) :
    domain (termEvaluation L Γ n M b e) = termSet L Γ n := domain_termRecursion _ _ _ _ _

theorem termEvaluation_boundVar {L n i : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (Γ M b e : V) (hi : i ∈ n) : (termEvaluation L Γ n M b e) ‘ (boundVarCode i) = b ‘ i := by
  exact (termRecursion_boundVar hL hn Γ (termEvaluationStep M b e) (by definability) hi).trans
    (termEvaluationStep_boundVar _ _ _ _ _)

theorem termEvaluation_freeVar {L n x : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (Γ M b e : V) (hx : x ∈ Γ) : (termEvaluation L Γ n M b e) ‘ (freeVarCode x) = e ‘ x := by
  exact (termRecursion_freeVar hL hn Γ (termEvaluationStep M b e) (by definability) hx).trans
    (termEvaluationStep_freeVar _ _ _ _ _)

theorem termEvaluation_function {L n f args : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (Γ M b e : V) (ht : functionTermCode f args ∈ termSet L Γ n) :
    (termEvaluation L Γ n M b e) ‘ (functionTermCode f args) =
      ((structureFunctions M) ‘ f) ‘ (compose args (termEvaluation L Γ n M b e)) := by
  have h := termRecursion_function hL hn Γ (termEvaluationStep M b e) (by definability) ht
  simpa only [termEvaluation, termEvaluationStep_function, compose_restrict_range] using h

theorem termEvaluation_value_mem {L n M b e : V} (hM : IsStructureCode L M)
    (hn : n ∈ (ω : V)) (Γ : V) (hb : b ∈ structureDomain M ^ n)
    (he : e ∈ structureDomain M ^ Γ) :
    ∀ t ∈ termSet L Γ n, (termEvaluation L Γ n M b e) ‘ t ∈ structureDomain M := by
  apply termSet_induction hM.language hn Γ
    (fun t ↦ (termEvaluation L Γ n M b e) ‘ t ∈ structureDomain M) (by definability)
  · intro i hi
    rw [termEvaluation_boundVar hM.language hn Γ M b e hi]
    exact function_value_mem hb hi
  · intro x hx
    rw [termEvaluation_freeVar hM.language hn Γ M b e hx]
    exact function_value_mem he hx
  · intro f hf args ha ih
    have ht := (functionTermCode_mem_iff hM.language hn Γ f args).mpr ⟨hf, ha⟩
    rw [termEvaluation_function hM.language hn Γ M b e ht]
    apply hM.function_value_mem hf
    apply compose_mem_function_of_values ha
    · intro t ht
      simpa using range_subset_of_mem_function ha t ht
    · exact ih

theorem termEvaluation_mem_function {L n M b e : V} (hM : IsStructureCode L M)
    (hn : n ∈ (ω : V)) (Γ : V) (hb : b ∈ structureDomain M ^ n)
    (he : e ∈ structureDomain M ^ Γ) :
    termEvaluation L Γ n M b e ∈ structureDomain M ^ (termSet L Γ n) := by
  have h := restrict_mem_function_of_values (f := termEvaluation L Γ n M b e)
    (A := termSet L Γ n) (by simp) (termEvaluation_value_mem hM hn Γ hb he)
  rw [IsFunction.restrict_eq_self (termEvaluation L Γ n M b e) (termSet L Γ n)
    (by simp)] at h
  exact h

theorem termEvaluation_eq_iff (L Γ n M b e g : V) :
    termEvaluation L Γ n M b e = g ↔
      IsRecursionAttempt (subtermRelation (termSet L Γ n)) (termSet L Γ n)
        (termEvaluationStep M b e) g ∧ domain g = termSet L Γ n :=
  wellFoundedRecursion_eq_iff (subtermRelation_wellFounded (termSet L Γ n))
    (termEvaluationStep M b e) (by definability) g

instance termEvaluation_definable :
    Language.DefinableFunction ℒₛₑₜ (fun v : Fin 6 → V ↦
      termEvaluation (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) := by
  have h : Language.Definable ℒₛₑₜ (fun v : Fin 7 → V ↦
      IsRecursionAttempt (subtermRelation (termSet (v 1) (v 2) (v 3)))
        (termSet (v 1) (v 2) (v 3)) (termEvaluationStep (v 4) (v 5) (v 6)) (v 0) ∧
      domain (v 0) = termSet (v 1) (v 2) (v 3)) := by
    unfold IsRecursionAttempt
    definability
  apply Language.Definable.of_iff h
  intro v
  exact eq_comm.trans (termEvaluation_eq_iff (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 0))

end ZFVP


