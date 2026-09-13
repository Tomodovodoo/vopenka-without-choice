import ZFVP.ModelTheory.InfinitaryEqualityDerivation

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace Formula
variable {L : Language}

@[simp] theorem subst_and {n m} (σ : Fin n → Semiterm L Empty m) (φ ψ : Formula L n) :
    (φ.and ψ).subst σ = (φ.subst σ).and (ψ.subst σ) := by
  apply congrArg Formula.conj
  funext i
  change (if i = 0 then φ else ψ).subst σ = if i = 0 then φ.subst σ else ψ.subst σ
  split_ifs <;> rfl

@[simp] theorem subst_or {n m} (σ : Fin n → Semiterm L Empty m) (φ ψ : Formula L n) :
    (φ.or ψ).subst σ = (φ.subst σ).or (ψ.subst σ) := by
  simp only [Formula.or, subst, subst_and]

@[simp] theorem subst_iff {n m} (σ : Fin n → Semiterm L Empty m) (φ ψ : Formula L n) :
    (φ.iff ψ).subst σ = (φ.subst σ).iff (ψ.subst σ) := by
  simp only [Formula.iff, subst_and, subst_imp]

@[simp] theorem subst_all {n m} (σ : Fin n → Semiterm L Empty m) (φ : Formula L (n + 1)) :
    (all φ).subst σ = all (φ.subst (liftSubstitution σ)) := rfl

theorem substFirst_lift {n m} (φ : Formula L (n + 1))
    (σ : Fin n → Semiterm L Empty m) (t : Semiterm L Empty m) :
    (φ.subst (liftSubstitution σ)).substFirst t = φ.subst (Fin.cases t σ) := by
  simp only [substFirst, ← rewrite_subst, rewrite_comp]
  congr 1
  apply Rew.ext
  · intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => simp only [Rew.comp_app, Rew.subst_bvar, liftSubstitution, Fin.cases_succ,
        ConstantTranslation.substFirst_bShift]
  · intro i; exact i.elim

@[simp] theorem expandFirstOrder_subst {n m} (σ : Fin n → Semiterm L Empty m)
    (φ : Semisentence L n) :
    (expandFirstOrder φ).subst σ = expandFirstOrder (φ ⇜ σ) := by
  induction φ generalizing m with
  | verum => rfl
  | falsum => rfl
  | rel r ts => rfl
  | nrel r ts => rfl
  | and φ ψ ihφ ihψ =>
    change ((expandFirstOrder φ).and (expandFirstOrder ψ)).subst σ =
      (expandFirstOrder (φ ⇜ σ)).and (expandFirstOrder (ψ ⇜ σ))
    rw [subst_and, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    change ((expandFirstOrder φ).or (expandFirstOrder ψ)).subst σ =
      (expandFirstOrder (φ ⇜ σ)).or (expandFirstOrder (ψ ⇜ σ))
    rw [subst_or, ihφ, ihψ]
  | all φ ih =>
    change all ((expandFirstOrder φ).subst (liftSubstitution σ)) =
      all (expandFirstOrder ((Rew.subst σ).q ▹ φ))
    rw [q_subst_eq, ih]
  | exs φ ih =>
    change Formula.exs ((expandFirstOrder φ).subst (liftSubstitution σ)) =
      .exs (expandFirstOrder ((Rew.subst σ).q ▹ φ))
    rw [q_subst_eq, ih]

end Formula
end ZFVP.Infinitary

