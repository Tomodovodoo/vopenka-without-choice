import ZFVP.SetTheory.LevyPrenex

/-! Alternating prenex forms, with one set quantifier per positive level and a bounded matrix. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

inductive IsLevyPrenex : LevyPolarity → ℕ → {n : ℕ} → SetTheorySemisentence n → Prop
  | bounded {p n} {φ : SetTheorySemisentence n} : IsBoundedSetFormula φ → IsLevyPrenex p 0 φ
  | exs {k n} {φ : SetTheorySemisentence (n + 1)} : IsLevyPrenex .pi k φ → IsLevyPrenex .sigma (k + 1) φ.exs
  | all {k n} {φ : SetTheorySemisentence (n + 1)} : IsLevyPrenex .sigma k φ → IsLevyPrenex .pi (k + 1) φ.all

theorem IsLevyPrenex.levy {p k n} {φ : SetTheorySemisentence n} (h : IsLevyPrenex p k φ) :
    IsLevyFormula p k φ := by
  induction h with
  | bounded h => exact .bounded h
  | exs _ ih => exact .exs ih.raise
  | all _ ih => exact .all ih.raise

def levyPrenexNormalForm (p : LevyPolarity) (k : ℕ) {n : ℕ}
    (φ : SetTheorySemisentence n) : SetTheorySemisentence n :=
  match k, p with
  | 0, _ => φ
  | k + 1, .sigma => (levyPrenexNormalForm .pi k (sigmaPrenexMatrix k φ)).exs
  | k + 1, .pi => (levyPrenexNormalForm .sigma k (piPrenexMatrix k φ)).all

theorem levyPrenexNormalForm_prenex {p k n} {φ : SetTheorySemisentence n}
    (hφ : IsLevyFormula p k φ) : IsLevyPrenex p k (levyPrenexNormalForm p k φ) := by
  induction k generalizing p n with
  | zero => exact .bounded (hφ.zero_bounded rfl)
  | succ k ih =>
    cases p with
    | sigma => exact .exs (ih (sigmaPrenexMatrix_pi k φ))
    | pi => exact .all (ih (piPrenexMatrix_sigma k φ))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem levyPrenexNormalForm_correct {p k n} {φ : SetTheorySemisentence n}
    (hφ : IsLevyFormula p k φ) (v : Fin n → V) :
    (levyPrenexNormalForm p k φ).Evalb v ↔ φ.Evalb v := by
  induction k generalizing p n with
  | zero => rfl
  | succ k ih =>
    cases p with
    | sigma =>
      apply Iff.trans _ (sigmaPrenexMatrix_correct hφ v)
      change (∃ x : V, (levyPrenexNormalForm .pi k (sigmaPrenexMatrix k φ)).Evalb (x :> v)) ↔
        ∃ x : V, (sigmaPrenexMatrix k φ).Evalb (x :> v)
      exact exists_congr fun x ↦ ih (sigmaPrenexMatrix_pi k φ) (x :> v)
    | pi =>
      apply Iff.trans _ (piPrenexMatrix_correct hφ v)
      change (∀ x : V, (levyPrenexNormalForm .sigma k (piPrenexMatrix k φ)).Evalb (x :> v)) ↔
        ∀ x : V, (piPrenexMatrix k φ).Evalb (x :> v)
      exact forall_congr' fun x ↦ ih (piPrenexMatrix_sigma k φ) (x :> v)

theorem levy_prenex_normal_form {p k n} {φ : SetTheorySemisentence n}
    (hφ : IsLevyFormula p k φ) :
    ∃ ψ : SetTheorySemisentence n, IsLevyPrenex p k ψ ∧
      ∀ v : Fin n → V, ψ.Evalb v ↔ φ.Evalb v :=
  ⟨levyPrenexNormalForm p k φ, levyPrenexNormalForm_prenex hφ, levyPrenexNormalForm_correct hφ⟩

end ZFVP
