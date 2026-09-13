import ZFVP.SetTheory.SameLevelForcing

/-! A forcing compiler whose input is finite syntax and a finite derivation.
No interpreted structure occurs in the definition of the output formula. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The positive-level derivations used by the forcing compiler, as data. -/
inductive PositiveLevyFormulaTree :
    LevyPolarity → ℕ → {n : ℕ} → SetTheorySemisentence n → Type
  | bounded {p k n} (t : BoundedFormulaTree n) :
      PositiveLevyFormulaTree p (k + 1) t.formula
  | raise {p q k n} {φ : SetTheorySemisentence n} :
      PositiveLevyFormulaTree p (k + 1) φ → PositiveLevyFormulaTree q (k + 2) φ
  | and {p k n} {φ ψ : SetTheorySemisentence n} :
      PositiveLevyFormulaTree p k φ → PositiveLevyFormulaTree p k ψ →
        PositiveLevyFormulaTree p k (φ.and ψ)
  | or {p k n} {φ ψ : SetTheorySemisentence n} :
      PositiveLevyFormulaTree p k φ → PositiveLevyFormulaTree p k ψ →
        PositiveLevyFormulaTree p k (φ.or ψ)
  | boundedAll {p k n} (t : SetTheorySemiterm Empty n) {φ : SetTheorySemisentence (n + 1)} :
      PositiveLevyFormulaTree p k φ → PositiveLevyFormulaTree p k (boundedSetAll t φ)
  | boundedExs {p k n} (t : SetTheorySemiterm Empty n) {φ : SetTheorySemisentence (n + 1)} :
      PositiveLevyFormulaTree p k φ → PositiveLevyFormulaTree p k (boundedSetExs t φ)
  | exs {k n} {φ : SetTheorySemisentence (n + 1)} :
      PositiveLevyFormulaTree .sigma (k + 1) φ → PositiveLevyFormulaTree .sigma (k + 1) φ.exs
  | all {k n} {φ : SetTheorySemisentence (n + 1)} :
      PositiveLevyFormulaTree .pi (k + 1) φ → PositiveLevyFormulaTree .pi (k + 1) φ.all

namespace PositiveLevyFormulaTree

theorem positive {p k n} {φ : SetTheorySemisentence n} (t : PositiveLevyFormulaTree p k φ) :
    0 < k := by
  induction t with
  | bounded => omega
  | raise => omega
  | and _ _ ih _ => exact ih
  | or _ _ ih _ => exact ih
  | boundedAll _ _ ih => exact ih
  | boundedExs _ _ ih => exact ih
  | exs => omega
  | all => omega

def forcing (symmetric : Bool) : {p : LevyPolarity} → {k n : ℕ} →
    {φ : SetTheorySemisentence n} → PositiveLevyFormulaTree p k φ →
      SetTheorySemisentence (n + 5)
  | p, _, _, _, .bounded t => t.levyForcingBase p
  | _, _, _, _, .raise t => t.forcing symmetric
  | _, _, _, _, .and t u => (t.forcing symmetric).and (u.forcing symmetric)
  | _, _, _, _, .or t u => levyForcingOrStep (t.forcing symmetric) (u.forcing symmetric)
  | p, _, _, _, .boundedAll x t => forcingTransitiveBind p (levyForcingBoundedAllBody x (t.forcing symmetric))
  | p, _, _, _, .boundedExs x t => forcingTransitiveBind p (levyForcingBoundedExsBody x (t.forcing symmetric))
  | _, _, _, _, .exs t => levyForcingExsStep symmetric (t.forcing symmetric)
  | _, _, _, _, .all t => levyForcingAllStep symmetric (t.forcing symmetric)

theorem forcing_levy {p k n} {φ : SetTheorySemisentence n}
    (t : PositiveLevyFormulaTree p k φ) (symmetric : Bool) :
    IsLevyFormula p k (t.forcing symmetric) := by
  induction t with
  | bounded t => exact t.levyForcingBase_levy _ (by omega)
  | raise _ ih => exact .raise ih
  | and _ _ iht ihu => exact .and iht ihu
  | or _ _ iht ihu => exact levyForcingOrStep_levy iht ihu
  | boundedAll x t ih => exact forcingTransitiveBind_levy t.positive (levyForcingBoundedAllBody_levy x ih)
  | boundedExs x t ih => exact forcingTransitiveBind_levy t.positive (levyForcingBoundedExsBody_levy x ih)
  | exs _ ih => exact levyForcingExsStep_sigma symmetric ih
  | all _ ih => exact levyForcingAllStep_pi symmetric ih

end PositiveLevyFormulaTree

theorem positiveLevyFormulaTree_nonempty {p k n} {φ : SetTheorySemisentence n}
    (hφ : IsLevyFormula p k φ) (hk : 0 < k) : Nonempty (PositiveLevyFormulaTree p k φ) := by
  induction hφ with
  | @bounded p k n φ hφ =>
    obtain ⟨t, rfl⟩ := boundedFormulaTree_exists hφ
    cases k with
    | zero => omega
    | succ k => exact ⟨.bounded t⟩
  | @raise p q k n φ hφ ih =>
    cases k with
    | zero =>
      obtain ⟨t, rfl⟩ := boundedFormulaTree_exists (hφ.zero_bounded rfl)
      exact ⟨.bounded t⟩
    | succ k =>
      obtain ⟨t⟩ := ih (by omega)
      exact ⟨.raise t⟩
  | and _ _ iht ihu =>
    obtain ⟨t⟩ := iht hk
    obtain ⟨u⟩ := ihu hk
    exact ⟨.and t u⟩
  | or _ _ iht ihu =>
    obtain ⟨t⟩ := iht hk
    obtain ⟨u⟩ := ihu hk
    exact ⟨.or t u⟩
  | boundedAll x _ ih =>
    obtain ⟨t⟩ := ih hk
    exact ⟨.boundedAll x t⟩
  | boundedExs x _ ih =>
    obtain ⟨t⟩ := ih hk
    exact ⟨.boundedExs x t⟩
  | exs _ ih =>
    obtain ⟨t⟩ := ih hk
    exact ⟨.exs t⟩
  | all _ ih =>
    obtain ⟨t⟩ := ih hk
    exact ⟨.all t⟩

/-- Reification chooses only a finite derivation of a fixed syntactic statement. -/
noncomputable def fixedLevyFormulaTree {p k n} {φ : SetTheorySemisentence n}
    (hφ : IsLevyFormula p k φ) (hk : 0 < k) : PositiveLevyFormulaTree p k φ :=
  Classical.choice (positiveLevyFormulaTree_nonempty hφ hk)

noncomputable def fixedOrdinaryForcingFormula {p k n} {φ : SetTheorySemisentence n}
    (hφ : IsLevyFormula p k φ) (hk : 0 < k) : SetTheorySemisentence (n + 3) :=
  ordinaryForcingSpecialization p ((fixedLevyFormulaTree hφ hk).forcing false)

theorem fixedOrdinaryForcingFormula_levy {p k n} {φ : SetTheorySemisentence n}
    (hφ : IsLevyFormula p k φ) (hk : 0 < k) :
    IsLevyFormula p k (fixedOrdinaryForcingFormula hφ hk) :=
  ordinaryForcingSpecialization_levy hk ((fixedLevyFormulaTree hφ hk).forcing_levy false)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem PositiveLevyFormulaTree.forcing_translation {p k n} {φ : SetTheorySemisentence n}
    (t : PositiveLevyFormulaTree p k φ) (symmetric : Bool) :
    IsForcingTranslation (V := V) symmetric φ (t.forcing symmetric) := by
  induction t with
  | bounded t => exact t.levyForcingBase_translation symmetric _
  | raise _ ih => exact ih
  | and _ _ iht ihu => exact iht.and ihu
  | or _ _ iht ihu => exact iht.or ihu
  | boundedAll x _ ih => exact ih.boundedAll x _
  | boundedExs x _ ih => exact ih.boundedExs x _
  | exs _ ih => exact ih.exs
  | all _ ih => exact ih.all

theorem eval_fixedOrdinaryForcingFormula {pol k n} {φ : SetTheorySemisentence n}
    (hφ : IsLevyFormula pol k φ) (hk : 0 < k) {P R : V} (hR : IsForcingPreorder P R)
    (v : Fin n → V) (hv : ∀ i, IsForcingName P (v i)) (p : V) :
    (fixedOrdinaryForcingFormula hφ hk).Evalb (P :> R :> p :> v) ↔
      p ∈ forcingFormula P R φ (standardTuple v) :=
  ordinaryForcingSpecialization_meaning ((fixedLevyFormulaTree hφ hk).forcing_translation false)
    pol hR v hv p

end ZFVP
