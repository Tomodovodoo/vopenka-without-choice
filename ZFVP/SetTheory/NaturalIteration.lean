import ZFVP.SetTheory.NaturalPredecessor
import ZFVP.SetTheory.FunctionValue
import Foundation.FirstOrder.SetTheory.Recursion

/-! Iteration of a definable operation through all internal natural numbers. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def naturalIterationStep (F : V → V) (a g : V) : V := by
  classical
  exact if domain g = 0 then a else F (g ‘ (⋃ˢ domain g))

theorem naturalIterationStep_definable (F : V → V) (hF : ℒₛₑₜ-function₁ F) (a : V) :
    ℒₛₑₜ-function₁ (naturalIterationStep F a) := by
  have h : ℒₛₑₜ-relation (fun z g : V ↦
      (domain g = 0 ∧ z = a) ∨ (domain g ≠ 0 ∧ z = F (g ‘ (⋃ˢ domain g)))) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = naturalIterationStep F a (v 1) ↔ _
  unfold naturalIterationStep
  split <;> simp_all

noncomputable def naturalIteration (F : V → V) (hF : ℒₛₑₜ-function₁ F) (a n : V) : V :=
  Replacement.transfiniteRec (naturalIterationStep F a) (naturalIterationStep_definable F hF a) n

instance naturalIteration_definable (F : V → V) (hF : ℒₛₑₜ-function₁ F) (a : V) :
    ℒₛₑₜ-function₁ (naturalIteration F hF a) :=
  Replacement.transfiniteRec_definable (naturalIterationStep_definable F hF a)

theorem naturalIteration_zero (F : V → V) (hF : ℒₛₑₜ-function₁ F) (a : V) :
    naturalIteration F hF a 0 = a := by
  have hr := Replacement.transfiniteRec_spec (naturalIterationStep F a)
    (naturalIterationStep_definable F hF a) (IsOrdinal.toOrdinal (0 : V))
  change naturalIteration F hF a 0 = naturalIterationStep F a
    (definableGraph 0 (naturalIteration F hF a) (by definability)) at hr
  simpa [naturalIterationStep, domain_definableGraph] using hr

theorem naturalIteration_succ (F : V → V) (hF : ℒₛₑₜ-function₁ F) (a : V)
    {n : V} (hn : n ∈ (ω : V)) : naturalIteration F hF a (succ n) = F (naturalIteration F hF a n) := by
  have : IsOrdinal n := IsOrdinal.of_mem hn
  have hr := Replacement.transfiniteRec_spec (naturalIterationStep F a)
    (naturalIterationStep_definable F hF a) (IsOrdinal.toOrdinal (succ n))
  change naturalIteration F hF a (succ n) = naturalIterationStep F a
    (definableGraph (succ n) (naturalIteration F hF a) (by definability)) at hr
  have hne : succ n ≠ (0 : V) := by
    intro h
    have hm : n ∈ succ n := by simp
    rw [h] at hm
    exact not_mem_empty hm
  simpa [naturalIterationStep, domain_definableGraph, hne, sUnion_succ_of_transitive,
    value_definableGraph _ _ _ (show n ∈ succ n by simp)] using hr

theorem naturalIteration_invariant (F : V → V) (hF : ℒₛₑₜ-function₁ F) (a : V)
    (P : V → Prop) (hP : ℒₛₑₜ-predicate P) (ha : P a) (hstep : ∀ x, P x → P (F x)) :
    ∀ n ∈ (ω : V), P (naturalIteration F hF a n) := by
  apply naturalNumber_induction (fun n ↦ P (naturalIteration F hF a n)) (by definability)
  · simpa only [naturalIteration_zero] using ha
  · intro n hn ih
    rw [naturalIteration_succ F hF a hn]
    exact hstep _ ih

noncomputable def naturalIterationGraph (F : V → V) (hF : ℒₛₑₜ-function₁ F) (a : V) : V :=
  definableGraph ω (naturalIteration F hF a) (by definability)

instance naturalIterationGraph_isFunction (F : V → V) (hF : ℒₛₑₜ-function₁ F) (a : V) :
    IsFunction (naturalIterationGraph F hF a) := definableGraph_isFunction _ _ _

@[simp] theorem domain_naturalIterationGraph (F : V → V) (hF : ℒₛₑₜ-function₁ F) (a : V) :
    domain (naturalIterationGraph F hF a) = ω := domain_definableGraph _ _ _

theorem naturalIterationGraph_value (F : V → V) (hF : ℒₛₑₜ-function₁ F) (a : V)
    {n : V} (hn : n ∈ (ω : V)) :
    (naturalIterationGraph F hF a) ‘ n = naturalIteration F hF a n := value_definableGraph _ _ _ hn

end ZFVP
