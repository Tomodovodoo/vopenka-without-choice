import ZFVP.ModelTheory.InfinitaryTermSubstitution
import ZFVP.ModelTheory.InfinitaryEquality

/-! First-order quantifier and equality schemas for arbitrary infinitary formulas. -/

namespace ZFVP.Infinitary

open LO LO.FirstOrder

namespace Formula

variable {L : Language} {n : ℕ}

def universalInstantiation (φ : Formula L (n + 1)) (t : Semiterm L Empty n) : Formula L n :=
  imp (all φ) (substFirst t φ)

def universalDistribution (φ ψ : Formula L (n + 1)) : Formula L n :=
  imp (all (imp φ ψ)) (imp (all φ) (all ψ))

/-- Monotonicity for the primitive existential constructor. This is needed separately
from universal distribution because `all` is defined using syntactic negation. -/
def existentialDistribution (φ ψ : Formula L (n + 1)) : Formula L n :=
  imp (all (imp φ ψ)) (imp (.exs φ) (.exs ψ))

def vacuousGeneralization (φ : Formula L n) : Formula L n :=
  imp φ (all (rename Fin.succ φ))

theorem eval_universalInstantiation {M : Type*} [Structure L M]
    (φ : Formula L (n + 1)) (t : Semiterm L Empty n) (b : Fin n → M) :
    Eval (universalInstantiation φ t) b := by
  simp only [universalInstantiation, eval_imp, eval_all, eval_substFirst]
  exact fun h ↦ h (t.val b Empty.elim)

theorem eval_universalDistribution {M : Type*} [Structure L M]
    (φ ψ : Formula L (n + 1)) (b : Fin n → M) : Eval (universalDistribution φ ψ) b := by
  simp only [universalDistribution, eval_imp, eval_all]
  exact fun h hφ x ↦ h x (hφ x)

theorem eval_existentialDistribution {M : Type*} [Structure L M]
    (φ ψ : Formula L (n + 1)) (b : Fin n → M) : Eval (existentialDistribution φ ψ) b := by
  simp only [existentialDistribution, eval_imp, eval_all, eval_exs]
  rintro h ⟨x, hx⟩
  exact ⟨x, h x hx⟩

theorem eval_vacuousGeneralization {M : Type*} [Structure L M]
    (φ : Formula L n) (b : Fin n → M) : Eval (vacuousGeneralization φ) b := by
  simp only [vacuousGeneralization, eval_imp, eval_all, eval_rename]
  intro h x
  have he : (x :> b) ∘ Fin.succ = b := by funext i; rfl
  simpa only [he] using h

section Equality

variable [L.Eq]

def termEqual (s t : Semiterm L Empty n) : Formula L n :=
  .fo (.rel Language.Eq.eq ![s, t])

@[simp] theorem eval_termEqual {M : Type*} [Structure L M] [Structure.Eq L M]
    (s t : Semiterm L Empty n) (b : Fin n → M) :
    Eval (termEqual s t) b ↔ s.val b Empty.elim = t.val b Empty.elim := by
  simp [termEqual, Semiformula.eval_rel]

def equalityReflexivity (t : Semiterm L Empty n) : Formula L n := termEqual t t

/-- Equal terms can replace one another even inside countable operations and Q. -/
def equalitySubstitution (φ : Formula L (n + 1)) (s t : Semiterm L Empty n) : Formula L n :=
  imp (termEqual s t) (iff (substFirst s φ) (substFirst t φ))

theorem eval_equalityReflexivity {M : Type*} [Structure L M] [Structure.Eq L M]
    (t : Semiterm L Empty n) (b : Fin n → M) : Eval (equalityReflexivity t) b := by
  simp [equalityReflexivity]

theorem eval_equalitySubstitution {M : Type*} [Structure L M] [Structure.Eq L M]
    (φ : Formula L (n + 1)) (s t : Semiterm L Empty n) (b : Fin n → M) :
    Eval (equalitySubstitution φ s t) b := by
  simp only [equalitySubstitution, eval_imp, eval_termEqual, eval_iff, eval_substFirst]
  intro h
  rw [h]

end Equality

end Formula

end ZFVP.Infinitary
