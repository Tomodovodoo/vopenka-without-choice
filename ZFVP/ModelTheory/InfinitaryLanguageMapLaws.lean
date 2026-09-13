import ZFVP.ModelTheory.InfinitaryLanguageMap
import ZFVP.ModelTheory.InfinitaryKeislerSoundness

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace Formula
variable {L K : Language} (η : L →ᵥ K)

@[simp] theorem lMap_neg {n} (φ : Formula L n) : (Formula.neg φ).lMap η = .neg (φ.lMap η) := rfl
@[simp] theorem lMap_conj {n} (φ : ℕ → Formula L n) : (Formula.conj φ).lMap η = .conj (fun i ↦ (φ i).lMap η) := rfl
@[simp] theorem lMap_exs {n} (φ : Formula L (n + 1)) : (Formula.exs φ).lMap η = .exs (φ.lMap η) := rfl
@[simp] theorem lMap_q {n} (φ : Formula L (n + 1)) : (Formula.q φ).lMap η = .q (φ.lMap η) := rfl
@[simp] theorem lMap_all {n} (φ : Formula L (n + 1)) : (all φ).lMap η = all (φ.lMap η) := rfl
@[simp] theorem lMap_and {n} (φ ψ : Formula L n) : (φ.and ψ).lMap η = (φ.lMap η).and (ψ.lMap η) := by
  change Formula.conj (fun i ↦ (if i = 0 then φ else ψ).lMap η) = _
  apply congrArg Formula.conj
  funext i
  split_ifs <;> rfl
@[simp] theorem lMap_or {n} (φ ψ : Formula L n) : (φ.or ψ).lMap η = (φ.lMap η).or (ψ.lMap η) := by
  simp only [Formula.or, lMap_neg, lMap_and]
@[simp] theorem lMap_imp {n} (φ ψ : Formula L n) : (φ.imp ψ).lMap η = (φ.lMap η).imp (ψ.lMap η) := by
  simp only [Formula.imp, lMap_or, lMap_neg]
@[simp] theorem lMap_iff {n} (φ ψ : Formula L n) : (φ.iff ψ).lMap η = (φ.lMap η).iff (ψ.lMap η) := by
  simp only [Formula.iff, lMap_and, lMap_imp]

@[simp] theorem lMap_rename {n m} (ρ : Fin n → Fin m) (φ : Formula L n) :
    (φ.rename ρ).lMap η = (φ.lMap η).rename ρ := by
  induction φ generalizing m with
  | fo φ => exact congrArg Formula.fo (Semiformula.lMap_map ρ id φ)
  | neg φ ih => exact congrArg Formula.neg (ih ρ)
  | conj φ ih => exact congrArg Formula.conj (funext fun i ↦ ih i ρ)
  | exs φ ih => exact congrArg Formula.exs (ih (liftRenaming ρ))
  | q φ ih => exact congrArg Formula.q (ih (liftRenaming ρ))

theorem lMap_liftSubstitution {n m} (σ : Fin n → Semiterm L Empty m) :
    (fun i ↦ (liftSubstitution σ i).lMap η) = liftSubstitution (fun i ↦ (σ i).lMap η) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => exact Semiterm.lMap_bShift η (σ i)

@[simp] theorem lMap_subst {n m} (σ : Fin n → Semiterm L Empty m) (φ : Formula L n) :
    (φ.subst σ).lMap η = (φ.lMap η).subst (fun i ↦ (σ i).lMap η) := by
  induction φ generalizing m with
  | fo φ => exact congrArg Formula.fo (Semiformula.lMap_subst σ φ)
  | neg φ ih => exact congrArg Formula.neg (ih σ)
  | conj φ ih => exact congrArg Formula.conj (funext fun i ↦ ih i σ)
  | exs φ ih =>
      change Formula.exs (lMap η (subst (liftSubstitution σ) φ)) = _
      apply congrArg Formula.exs
      rw [ih, lMap_liftSubstitution]

  | q φ ih =>
      change Formula.q (lMap η (subst (liftSubstitution σ) φ)) = _
      apply congrArg Formula.q
      rw [ih, lMap_liftSubstitution]


@[simp] theorem lMap_substFirst {n} (t : Semiterm L Empty n) (φ : Formula L (n + 1)) :
    (φ.substFirst t).lMap η = (φ.lMap η).substFirst (t.lMap η) := by
  simp only [substFirst, lMap_subst]
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

@[simp] theorem lMap_expandFirstOrder {n} (φ : Semisentence L n) :
    (expandFirstOrder φ).lMap η = expandFirstOrder (φ.lMap η) := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r ts => rfl
  | nrel r ts => rfl
  | and φ ψ ihφ ihψ =>
      change ((expandFirstOrder φ).and (expandFirstOrder ψ)).lMap η =
        (expandFirstOrder (φ.lMap η)).and (expandFirstOrder (ψ.lMap η))
      rw [lMap_and, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      change ((expandFirstOrder φ).or (expandFirstOrder ψ)).lMap η =
        (expandFirstOrder (φ.lMap η)).or (expandFirstOrder (ψ.lMap η))
      rw [lMap_or, ihφ, ihψ]
  | all φ ih => exact congrArg Formula.all ih
  | exs φ ih => exact congrArg Formula.exs ih

@[simp] theorem lMap_termEqual [L.Eq] [K.Eq] (he : η.rel Language.Eq.eq = Language.Eq.eq)
    {n} (s t : Semiterm L Empty n) :
    (termEqual s t).lMap η = termEqual (s.lMap η) (t.lMap η) := by
  change Formula.fo (.rel (η.rel Language.Eq.eq) (fun i ↦ (![s, t] i).lMap η)) = _
  rw [he]
  congr 2
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
      | zero => rfl
      | succ i => exact i.elim0

@[simp] theorem lMap_equal [L.Eq] [K.Eq] (he : η.rel Language.Eq.eq = Language.Eq.eq)
    {n} (i j : Fin n) : (equal (L := L) i j).lMap η = equal (L := K) i j :=
  lMap_termEqual η he (.bvar i) (.bvar j)

end Formula
end ZFVP.Infinitary

