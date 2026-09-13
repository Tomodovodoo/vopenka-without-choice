import ZFVP.ModelTheory.InfinitaryFiniteProjection

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace Formula
variable {L : Language} {M : Type*} [Structure L M] (Q : Set M → Prop)

/-- Delete the coordinates existentially quantified by `exsN`. -/
def dropFirst : (k : ℕ) → {n : ℕ} → (Fin (n + k) → M) → (Fin n → M)
  | 0, _, b => b
  | k + 1, _, b => dropFirst k (fun i ↦ b i.succ)

theorem weakEval_exsN_iff (k : ℕ) {n} (φ : Formula L (n + k)) (b : Fin n → M) :
    WeakEval Q (exsN k φ) b ↔
      ∃ e : Fin (n + k) → M, dropFirst k e = b ∧ WeakEval Q φ e := by
  induction k with
  | zero =>
    constructor
    · intro h; exact ⟨b, rfl, h⟩
    · rintro ⟨e, rfl, h⟩; exact h
  | succ k ih =>
    change WeakEval Q (exsN k (.exs φ)) b ↔ _
    rw [ih]
    constructor
    · rintro ⟨e, he, x, hx⟩
      exact ⟨x :> e, he, hx⟩
    · rintro ⟨e, he, hx⟩
      refine ⟨(fun i ↦ e i.succ), he, e 0, ?_⟩
      have heq : (e 0 :> (fun i : Fin (n + k) ↦ e i.succ)) = e := by
        funext i
        cases i using Fin.cases <;> rfl
      rwa [heq]

def lastCoordinate : (k : ℕ) → Fin (1 + k)
  | 0 => 0
  | k + 1 => (lastCoordinate k).succ

theorem lastCoordinate_val (k : ℕ) : (lastCoordinate k).val = k := by
  induction k with
  | zero => rfl
  | succ k ih => change (lastCoordinate k).val + 1 = k + 1; rw [ih]

theorem dropFirst_one (k : ℕ) (e : Fin (1 + k) → M) :
    dropFirst k e = (e (lastCoordinate k) :> Fin.elim0) := by
  induction k with
  | zero =>
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact i.elim0
  | succ k ih => exact ih (fun i ↦ e i.succ)

theorem weakEval_exsN_one_iff (k : ℕ) (φ : Formula L (1 + k)) (x : M) :
    WeakEval Q (exsN k φ) (x :> Fin.elim0) ↔
      ∃ e : Fin (1 + k) → M, e (lastCoordinate k) = x ∧ WeakEval Q φ e := by
  rw [weakEval_exsN_iff]
  apply exists_congr
  intro e
  rw [dropFirst_one]
  constructor
  · rintro ⟨he, h⟩
    exact ⟨congrFun he 0, h⟩
  · rintro ⟨he, h⟩
    exact ⟨by rw [he], h⟩

end Formula
end ZFVP.Infinitary

