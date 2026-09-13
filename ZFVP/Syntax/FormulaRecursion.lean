import ZFVP.Syntax.Subformulas

/-! Internal recursion over context/formula pairs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def formulaRecursion (L Γ : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) : V :=
  wellFoundedRecursion (subformulaRelation_wellFounded (formulaFamily L Γ)) F hF

instance formulaRecursion_isFunction (L Γ : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    IsFunction (formulaRecursion L Γ F hF) := wellFoundedRecursion_isFunction _ _ _

@[simp] theorem domain_formulaRecursion (L Γ : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    domain (formulaRecursion L Γ F hF) = formulaFamily L Γ := domain_wellFoundedRecursion _ _ _

theorem formulaRecursion_value (L Γ : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F)
    {t : V} (ht : t ∈ formulaFamily L Γ) :
    (formulaRecursion L Γ F hF) ‘ t = F t ((formulaRecursion L Γ F hF) ↾
      (predecessors (subformulaRelation (formulaFamily L Γ)) (formulaFamily L Γ) t)) :=
  wellFoundedRecursion_value _ _ _ ht

theorem formulaRecursion_previous_value {L Γ s t : V} (hL : IsLanguageCode L)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (ht : t ∈ formulaFamily L Γ)
    (hst : IsImmediateSubformula s t) :
    ((formulaRecursion L Γ F hF) ↾
      (predecessors (subformulaRelation (formulaFamily L Γ)) (formulaFamily L Γ) t)) ‘ s =
      (formulaRecursion L Γ F hF) ‘ s := by
  have hs := immediateSubformula_mem_family hL ht hst
  apply value_restrict (by simpa using hs)
  exact (mem_predecessors_iff _ _ _ _).mpr ⟨hs, (subformulaRelation_mem_iff hL ht).mpr hst⟩

theorem formulaRecursion_eq_iff (L Γ : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (g : V) :
    formulaRecursion L Γ F hF = g ↔
      IsRecursionAttempt (subformulaRelation (formulaFamily L Γ)) (formulaFamily L Γ) F g ∧
      domain g = formulaFamily L Γ :=
  wellFoundedRecursion_eq_iff (subformulaRelation_wellFounded (formulaFamily L Γ)) F hF g

end ZFVP
