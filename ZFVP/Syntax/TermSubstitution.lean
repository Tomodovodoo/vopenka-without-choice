import ZFVP.Syntax.TermEvaluation

/-! Simultaneous substitution of internal bound and free variables by term codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

attribute [local aesop 4 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def termSubstitutionStep (b e t previous : V) : V := by
  classical
  exact if kpair.π₁ t = 0 then b ‘ (kpair.π₂ t)
    else if kpair.π₁ t = 1 then e ‘ (kpair.π₂ t)
    else functionTermCode (kpair.π₁ (kpair.π₂ t)) (compose (kpair.π₂ (kpair.π₂ t)) previous)

instance termSubstitutionStep_definable : ℒₛₑₜ-function₄[V] termSubstitutionStep := by
  have h : ℒₛₑₜ-relation₅ (fun z b e t previous : V ↦
      (kpair.π₁ t = 0 ∧ z = b ‘ (kpair.π₂ t)) ∨
      (kpair.π₁ t ≠ 0 ∧ kpair.π₁ t = 1 ∧ z = e ‘ (kpair.π₂ t)) ∨
      (kpair.π₁ t ≠ 0 ∧ kpair.π₁ t ≠ 1 ∧ z =
        functionTermCode (kpair.π₁ (kpair.π₂ t)) (compose (kpair.π₂ (kpair.π₂ t)) previous))) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = termSubstitutionStep (v 1) (v 2) (v 3) (v 4) ↔ _
  unfold termSubstitutionStep
  split <;> simp_all
  split <;> simp_all

@[simp] theorem termSubstitutionStep_boundVar (b e i previous : V) :
    termSubstitutionStep b e (boundVarCode i) previous = b ‘ i := by
  simp [termSubstitutionStep, boundVarCode]

@[simp] theorem termSubstitutionStep_freeVar (b e x previous : V) :
    termSubstitutionStep b e (freeVarCode x) previous = e ‘ x := by
  simp [termSubstitutionStep, freeVarCode]

@[simp] theorem termSubstitutionStep_function (b e f args previous : V) :
    termSubstitutionStep b e (functionTermCode f args) previous =
      functionTermCode f (compose args previous) := by
  have h20 : (2 : V) ≠ 0 := by
    intro h
    have := (natCast_eq_iff (V := V) 2 0).mp h
    contradiction
  have h21 : (2 : V) ≠ 1 := by
    intro h
    have := (natCast_eq_iff (V := V) 2 1).mp h
    contradiction
  simp [termSubstitutionStep, functionTermCode, h20, h21]

noncomputable def termSubstitution (L Γ n b e : V) : V :=
  termRecursion L Γ n (termSubstitutionStep b e) (by definability)

instance termSubstitution_isFunction (L Γ n b e : V) : IsFunction (termSubstitution L Γ n b e) :=
  termRecursion_isFunction _ _ _ _ _

@[simp] theorem domain_termSubstitution (L Γ n b e : V) :
    domain (termSubstitution L Γ n b e) = termSet L Γ n := domain_termRecursion _ _ _ _ _

theorem termSubstitution_boundVar {L n i : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (Γ b e : V) (hi : i ∈ n) : (termSubstitution L Γ n b e) ‘ (boundVarCode i) = b ‘ i := by
  exact (termRecursion_boundVar hL hn Γ (termSubstitutionStep b e) (by definability) hi).trans
    (termSubstitutionStep_boundVar _ _ _ _)

theorem termSubstitution_freeVar {L n x : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (Γ b e : V) (hx : x ∈ Γ) : (termSubstitution L Γ n b e) ‘ (freeVarCode x) = e ‘ x := by
  exact (termRecursion_freeVar hL hn Γ (termSubstitutionStep b e) (by definability) hx).trans
    (termSubstitutionStep_freeVar _ _ _ _)

theorem termSubstitution_function {L n f args : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (Γ b e : V) (ht : functionTermCode f args ∈ termSet L Γ n) :
    (termSubstitution L Γ n b e) ‘ (functionTermCode f args) =
      functionTermCode f (compose args (termSubstitution L Γ n b e)) := by
  simpa only [termSubstitution, termSubstitutionStep_function, compose_restrict_range] using
    termRecursion_function hL hn Γ (termSubstitutionStep b e) (by definability) ht

theorem termSubstitution_value_mem {L Γ Δ n m b e : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hb : b ∈ termSet L Δ m ^ n) (he : e ∈ termSet L Δ m ^ Γ) :
    ∀ t ∈ termSet L Γ n, (termSubstitution L Γ n b e) ‘ t ∈ termSet L Δ m := by
  apply termSet_induction hL hn Γ
    (fun t ↦ (termSubstitution L Γ n b e) ‘ t ∈ termSet L Δ m) (by definability)
  · intro i hi
    rw [termSubstitution_boundVar hL hn Γ b e hi]
    exact function_value_mem hb hi
  · intro x hx
    rw [termSubstitution_freeVar hL hn Γ b e hx]
    exact function_value_mem he hx
  · intro f hf args ha ih
    have ht := (termSet_closed hL hn Γ).2.2 f hf args ha
    rw [termSubstitution_function hL hn Γ b e ht]
    apply (termSet_closed hL hm Δ).2.2 f hf
    exact compose_mem_function_of_values ha
      (fun t ht ↦ by simpa using range_subset_of_mem_function ha t ht) ih

theorem termSubstitution_mem_function {L Γ Δ n m b e : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hb : b ∈ termSet L Δ m ^ n) (he : e ∈ termSet L Δ m ^ Γ) :
    termSubstitution L Γ n b e ∈ termSet L Δ m ^ termSet L Γ n := by
  have h := restrict_mem_function_of_values (f := termSubstitution L Γ n b e)
    (A := termSet L Γ n) (by simp) (termSubstitution_value_mem hL hn hm hb he)
  rw [IsFunction.restrict_eq_self (termSubstitution L Γ n b e) (termSet L Γ n) (by simp)] at h
  exact h

theorem termSubstitution_eq_iff (L Γ n b e g : V) :
    termSubstitution L Γ n b e = g ↔
      IsRecursionAttempt (subtermRelation (termSet L Γ n)) (termSet L Γ n)
        (termSubstitutionStep b e) g ∧ domain g = termSet L Γ n :=
  wellFoundedRecursion_eq_iff (subtermRelation_wellFounded (termSet L Γ n))
    (termSubstitutionStep b e) (by definability) g

instance termSubstitution_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (termSubstitution (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun g L Γ n b e : V ↦
      IsRecursionAttempt (subtermRelation (termSet L Γ n)) (termSet L Γ n)
        (termSubstitutionStep b e) g ∧ domain g = termSet L Γ n) := by
    unfold IsRecursionAttempt
    definability
  apply Language.Definable.of_iff h
  intro v
  exact eq_comm.trans (termSubstitution_eq_iff (v 1) (v 2) (v 3) (v 4) (v 5) (v 0))

end ZFVP
