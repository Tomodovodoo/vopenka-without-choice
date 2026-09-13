import ZFVP.SetTheory.BoundedFormulas

/-! The closure presentation of the Levy hierarchy on external finite syntax.
Equivalence with prenex presentations and internal code predicates is separate. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

inductive LevyPolarity
  | sigma
  | pi
  deriving DecidableEq

def LevyPolarity.dual : LevyPolarity → LevyPolarity
  | .sigma => .pi
  | .pi => .sigma

@[simp] theorem LevyPolarity.dual_dual (p : LevyPolarity) : p.dual.dual = p := by cases p <;> rfl

inductive IsLevyFormula : LevyPolarity → ℕ → {n : ℕ} → SetTheorySemisentence n → Prop
  | bounded {p k n} {φ : SetTheorySemisentence n} : IsBoundedSetFormula φ → IsLevyFormula p k φ
  | raise {p q k n} {φ : SetTheorySemisentence n} : IsLevyFormula p k φ → IsLevyFormula q (k + 1) φ
  | and {p k n} {φ ψ : SetTheorySemisentence n} :
      IsLevyFormula p k φ → IsLevyFormula p k ψ → IsLevyFormula p k (.and φ ψ)
  | or {p k n} {φ ψ : SetTheorySemisentence n} :
      IsLevyFormula p k φ → IsLevyFormula p k ψ → IsLevyFormula p k (.or φ ψ)
  | boundedAll {p k n} (t : SetTheorySemiterm Empty n) {φ : SetTheorySemisentence (n + 1)} :
      IsLevyFormula p k φ → IsLevyFormula p k (boundedSetAll t φ)
  | boundedExs {p k n} (t : SetTheorySemiterm Empty n) {φ : SetTheorySemisentence (n + 1)} :
      IsLevyFormula p k φ → IsLevyFormula p k (boundedSetExs t φ)
  | exs {k n} {φ : SetTheorySemisentence (n + 1)} :
      IsLevyFormula .sigma (k + 1) φ → IsLevyFormula .sigma (k + 1) (.exs φ)
  | all {k n} {φ : SetTheorySemisentence (n + 1)} :
      IsLevyFormula .pi (k + 1) φ → IsLevyFormula .pi (k + 1) (.all φ)

abbrev IsSigmaFormula (k : ℕ) {n : ℕ} (φ : SetTheorySemisentence n) := IsLevyFormula .sigma k φ
abbrev IsPiFormula (k : ℕ) {n : ℕ} (φ : SetTheorySemisentence n) := IsLevyFormula .pi k φ

theorem IsLevyFormula.neg {p k n} {φ : SetTheorySemisentence n} (h : IsLevyFormula p k φ) :
    IsLevyFormula p.dual k (∼φ) := by
  induction h with
  | bounded hφ => exact .bounded hφ.neg
  | raise hφ ih => exact .raise ih
  | and hφ hψ ihφ ihψ => exact .or ihφ ihψ
  | or hφ hψ ihφ ihψ => exact .and ihφ ihψ
  | boundedAll t hφ ih => exact .boundedExs t ih
  | boundedExs t hφ ih => exact .boundedAll t ih
  | exs hφ ih => exact .all ih
  | all hφ ih => exact .exs ih

theorem isLevyFormula_neg_iff {p k n} {φ : SetTheorySemisentence n} :
    IsLevyFormula p.dual k (∼φ) ↔ IsLevyFormula p k φ := by
  constructor
  · intro h
    simpa using h.neg
  · exact IsLevyFormula.neg

theorem IsLevyFormula.mono {p k l n} {φ : SetTheorySemisentence n} (h : IsLevyFormula p k φ)
    (hkl : k ≤ l) : IsLevyFormula p l φ := by
  induction hkl with
  | refl => exact h
  | step hkl ih => exact .raise ih

theorem IsLevyFormula.zero_bounded {p k n} {φ : SetTheorySemisentence n} (h : IsLevyFormula p k φ)
    (hk : k = 0) : IsBoundedSetFormula φ := by
  induction h with
  | bounded hφ => exact hφ
  | raise hφ ih => cases hk
  | and hφ hψ ihφ ihψ => exact .and (ihφ hk) (ihψ hk)
  | or hφ hψ ihφ ihψ => exact .or (ihφ hk) (ihψ hk)
  | boundedAll t hφ ih => exact .all t (ih hk)
  | boundedExs t hφ ih => exact .exs t (ih hk)
  | exs hφ ih => cases hk
  | all hφ ih => cases hk

theorem isLevyFormula_zero_iff {p n} {φ : SetTheorySemisentence n} :
    IsLevyFormula p 0 φ ↔ IsBoundedSetFormula φ := ⟨fun h ↦ h.zero_bounded rfl, IsLevyFormula.bounded⟩

end ZFVP
