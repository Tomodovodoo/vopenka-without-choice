import ZFVP.ModelTheory.InfinitaryHenkinTruth

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace Formula
variable {L : Language} [L.Eq]

@[simp] theorem subst_termEqual {n m} (σ : Fin n → Semiterm L Empty m)
    (s t : Semiterm L Empty n) :
    (termEqual s t).subst σ = termEqual ((Rew.subst σ) s) ((Rew.subst σ) t) := by
  simp [termEqual, subst]

@[simp] theorem substFirst_termEqual {n} (u : Semiterm L Empty n)
    (s t : Semiterm L Empty (n + 1)) :
    (termEqual s t).substFirst u =
      termEqual ((Rew.subst (Fin.cases u Semiterm.bvar)) s)
        ((Rew.subst (Fin.cases u Semiterm.bvar)) t) := subst_termEqual _ s t

@[simp] theorem term_substFirst_bShift {n} (s t : Semiterm L Empty n) :
    (Rew.subst (Fin.cases s Semiterm.bvar)) (Rew.bShift t) = t :=
  ConstantTranslation.substFirst_bShift s t

end Formula

/-- Replace one coordinate by the newly bound variable, shifting all other terms. -/
def oneVariableSubstitution {L : Language} {n m} (σ : Fin n → Semiterm L Empty m)
    (i : Fin n) : Fin n → Semiterm L Empty (m + 1) :=
  fun j ↦ if j = i then .bvar 0 else Rew.bShift (σ j)

namespace Formula
variable {L : Language}

theorem term_subst_closed {n} (σ : Fin n → Semiterm L Empty 0)
    (t : Semiterm L Empty 0) :
    (Rew.subst σ) ((Rew.map (Fin.elim0 : Fin 0 → Fin n) id) t) = t := by
  have he : (Rew.subst σ).comp (Rew.map (Fin.elim0 : Fin 0 → Fin n) id) = Rew.id := by
    apply Rew.ext
    · intro i; exact i.elim0
    · intro i; exact i.elim
  simpa only [Rew.comp_app, Rew.id_app] using congrArg (fun w ↦ w t) he

theorem substFirst_oneVariable {n m} (φ : Formula L n)
    (σ : Fin n → Semiterm L Empty m) (i : Fin n) (t : Semiterm L Empty m) :
    (φ.subst (oneVariableSubstitution σ i)).substFirst t = φ.subst (Function.update σ i t) := by
  simp only [substFirst, ← rewrite_subst, rewrite_comp]
  congr 1
  apply Rew.ext
  · intro j
    by_cases h : j = i
    · subst j
      simp [Rew.comp_app, oneVariableSubstitution]
    · simp [Rew.comp_app, oneVariableSubstitution, h, ConstantTranslation.substFirst_bShift,
        Function.update_of_ne h]
  · intro j
    exact j.elim

end Formula
namespace KeislerDerivation
variable {L : Language} [L.Eq] {Γ : Set (Sentence L)}

theorem equality_symm {n} {s t : Semiterm L Empty n}
    (h : KeislerDerivation Γ (Formula.termEqual s t)) :
    KeislerDerivation Γ (Formula.termEqual t s) := by
  have hi := KeislerDerivation.mp
    (.eqSubst (Formula.termEqual (.bvar 0) (Rew.bShift s)) s t) h
  simp only [Formula.substFirst_termEqual, Rew.subst_bvar,
    Fin.cases_zero, Formula.term_substFirst_bShift] at hi
  exact KeislerDerivation.mp hi.iff_left (.eqRefl s)

theorem equality_trans {n} {r s t : Semiterm L Empty n}
    (h : KeislerDerivation Γ (Formula.termEqual r s))
    (g : KeislerDerivation Γ (Formula.termEqual s t)) :
    KeislerDerivation Γ (Formula.termEqual r t) := by
  have hi := KeislerDerivation.mp
    (.eqSubst (Formula.termEqual (Rew.bShift r) (.bvar 0)) s t) g
  simp only [Formula.substFirst_termEqual, Rew.subst_bvar,
    Fin.cases_zero, Formula.term_substFirst_bShift] at hi
  exact KeislerDerivation.mp hi.iff_left h

end KeislerDerivation
end ZFVP.Infinitary
