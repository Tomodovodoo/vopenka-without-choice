import Foundation.FirstOrder.Basic.Semantics.Semantics
import Mathlib.Data.Set.Countable

/-! Finitely many free variables, countable Boolean operations, and the standard
uncountability quantifier. First-order formulas retain their Foundation syntax. -/

namespace ZFVP.Infinitary
open LO LO.FirstOrder

inductive Formula (L : Language) : ℕ → Type _ where
  | fo {n : ℕ} : Semisentence L n → Formula L n
  | neg {n : ℕ} : Formula L n → Formula L n
  | conj {n : ℕ} : (ℕ → Formula L n) → Formula L n
  | exs {n : ℕ} : Formula L (n + 1) → Formula L n
  | q {n : ℕ} : Formula L (n + 1) → Formula L n

abbrev Sentence (L : Language) := Formula L 0

namespace Formula
variable {L : Language} {M : Type*} [Structure L M]

def Eval : {n : ℕ} → Formula L n → (Fin n → M) → Prop
  | _, .fo φ, b => φ.Evalb b
  | _, .neg φ, b => ¬Eval φ b
  | _, .conj φ, b => ∀ i : ℕ, Eval (φ i) b
  | _, .exs φ, b => ∃ x : M, Eval φ (x :> b)
  | _, .q φ, b => ¬Set.Countable {x : M | Eval φ (x :> b)}

def disj {n : ℕ} (φ : ℕ → Formula L n) : Formula L n := .neg (.conj fun i ↦ .neg (φ i))
def all {n : ℕ} (φ : Formula L (n + 1)) : Formula L n := .neg (.exs (.neg φ))
def and {n : ℕ} (φ ψ : Formula L n) : Formula L n := .conj fun i ↦ if i = 0 then φ else ψ
def or {n : ℕ} (φ ψ : Formula L n) : Formula L n := .neg (and (.neg φ) (.neg ψ))
def imp {n : ℕ} (φ ψ : Formula L n) : Formula L n := or (.neg φ) ψ
def iff {n : ℕ} (φ ψ : Formula L n) : Formula L n := and (imp φ ψ) (imp ψ φ)

@[simp] theorem eval_fo {n : ℕ} (φ : Semisentence L n) (b : Fin n → M) :
    Eval (.fo φ) b ↔ φ.Evalb b := Iff.rfl
@[simp] theorem eval_neg {n : ℕ} (φ : Formula L n) (b : Fin n → M) :
    Eval (.neg φ) b ↔ ¬Eval φ b := Iff.rfl
@[simp] theorem eval_conj {n : ℕ} (φ : ℕ → Formula L n) (b : Fin n → M) :
    Eval (.conj φ) b ↔ ∀ i, Eval (φ i) b := Iff.rfl
@[simp] theorem eval_exs {n : ℕ} (φ : Formula L (n + 1)) (b : Fin n → M) :
    Eval (.exs φ) b ↔ ∃ x : M, Eval φ (x :> b) := Iff.rfl
@[simp] theorem eval_q {n : ℕ} (φ : Formula L (n + 1)) (b : Fin n → M) :
    Eval (.q φ) b ↔ ¬Set.Countable {x : M | Eval φ (x :> b)} := Iff.rfl
@[simp] theorem eval_disj {n : ℕ} (φ : ℕ → Formula L n) (b : Fin n → M) :
    Eval (disj φ) b ↔ ∃ i, Eval (φ i) b := by
  classical
  simp [disj]
@[simp] theorem eval_all {n : ℕ} (φ : Formula L (n + 1)) (b : Fin n → M) :
    Eval (all φ) b ↔ ∀ x : M, Eval φ (x :> b) := by
  classical
  simp [all]
@[simp] theorem eval_and {n : ℕ} (φ ψ : Formula L n) (b : Fin n → M) :
    Eval (and φ ψ) b ↔ Eval φ b ∧ Eval ψ b := by
  classical
  simp only [and, eval_conj]
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1⟩
  · rintro ⟨hφ, hψ⟩ i
    split_ifs <;> assumption
@[simp] theorem eval_or {n : ℕ} (φ ψ : Formula L n) (b : Fin n → M) :
    Eval (or φ ψ) b ↔ Eval φ b ∨ Eval ψ b := by
  classical
  simp [or]
  tauto
@[simp] theorem eval_imp {n : ℕ} (φ ψ : Formula L n) (b : Fin n → M) :
    Eval (imp φ ψ) b ↔ (Eval φ b → Eval ψ b) := by
  classical
  simp [imp]
  tauto
@[simp] theorem eval_iff {n : ℕ} (φ ψ : Formula L n) (b : Fin n → M) :
    Eval (iff φ ψ) b ↔ (Eval φ b ↔ Eval ψ b) := by simp [iff, iff_def]

end Formula

def Satisfiable {L : Language} (φ : Sentence L) : Prop :=
  ∃ M : Type, ∃ _ : Nonempty M, ∃ s : Structure L M, @Formula.Eval L M s 0 φ ![]

end ZFVP.Infinitary
