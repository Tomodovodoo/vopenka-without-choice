import ZFVP.Syntax.EndExtensionTerms
import ZFVP.Syntax.TermEvaluation
import ZFVP.SetTheory.EndExtensionRelations
import ZFVP.SetTheory.UniformFunctionOperations

/-! Internal term evaluation agrees across ZF end extensions, by uniqueness of recursion. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_termPredecessors (j : MembershipEndExtension V W) {L Γ n t : V}
    (hL : IsLanguageCode L) (hn : n ∈ (ω : V)) (ht : t ∈ termSet L Γ n) :
    j (predecessors (subtermRelation (termSet L Γ n)) (termSet L Γ n) t) =
      predecessors (subtermRelation (termSet (j L) (j Γ) (j n))) (termSet (j L) (j Γ) (j n)) (j t) := by
  have hL' := (j.languageCode_iff L).mpr hL
  have hn' := (j.natural_iff n).mpr hn
  have ht' : j t ∈ termSet (j L) (j Γ) (j n) := by
    rw [← j.map_termSet hL hn Γ]; exact (j.mem_iff _ _).mpr ht
  rcases termSet_cases hL hn Γ ht with ⟨i, _, rfl⟩ | ⟨x, _, rfl⟩ | ⟨f, _, args, _, rfl⟩
  · rw [j.map_boundVarCode, predecessors_boundVarCode, predecessors_boundVarCode, j.map_empty]
  · rw [j.map_freeVarCode, predecessors_freeVarCode, predecessors_freeVarCode, j.map_empty]
  · rw [predecessors_functionTermCode hL hn Γ ht, j.map_range, j.map_functionTermCode]
    exact (predecessors_functionTermCode hL' hn' (j Γ) (by simpa only [j.map_functionTermCode] using ht')).symm

theorem map_termEvaluationStep (j : MembershipEndExtension V W) (M b e t previous : V) :
    j (termEvaluationStep M b e t previous) =
      termEvaluationStep (j M) (j b) (j e) (j t) (j previous) := by
  have hzero : j (0 : V) = (0 : W) := j.map_numeral 0
  have hone : j (1 : V) = (1 : W) := j.map_numeral 1
  have hz : kpair.π₁ (j t) = (0 : W) ↔ kpair.π₁ t = (0 : V) := by
    rw [← j.map_first, ← hzero, j.injective.eq_iff]
  have ho : kpair.π₁ (j t) = (1 : W) ↔ kpair.π₁ t = (1 : V) := by
    rw [← j.map_first, ← hone, j.injective.eq_iff]
  simp only [termEvaluationStep, hz, ho]
  split_ifs <;> simp only [j.map_value_total, j.map_first, j.map_second, j.map_compose, j.map_structureFunctions]
  all_goals tauto

theorem map_termEvaluation (j : MembershipEndExtension V W) {L n : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (Γ M b e : V) :
    j (termEvaluation L Γ n M b e) = termEvaluation (j L) (j Γ) (j n) (j M) (j b) (j e) := by
  symm
  apply (termEvaluation_eq_iff _ _ _ _ _ _ _).mpr
  rw [totalRecursionAttempt_iff]
  refine ⟨j.map_function _, ?_, ?_⟩
  · rw [← j.map_domain, domain_termEvaluation, j.map_termSet hL hn Γ]
  · intro u hu
    rw [← j.map_termSet hL hn Γ] at hu
    obtain ⟨t, ht, rfl⟩ := j.endExtension _ u hu
    rw [← j.map_value_total]
    have hrec := ((termEvaluation_eq_iff L Γ n M b e _).mp rfl).1.2.2 t (by simpa using ht)
    rw [hrec, j.map_termEvaluationStep, j.map_restrict, j.map_termPredecessors hL hn ht]

end MembershipEndExtension
end ZFVP
