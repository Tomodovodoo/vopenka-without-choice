import Foundation.FirstOrder.Basic.Calculus
import Foundation.FirstOrder.SetTheory.ZF

/-! Finite bound-variable presentations of proof formulas.
Free variables above the chosen bound are identified with the final variable.
Increasing the bound by one commutes with the eigenvariable shift. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def finiteVariableIndex (k j : ℕ) : Fin (k + 1) := ⟨min j k, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

def finiteVariableBase (k : ℕ) : Rew ℒₛₑₜ ℕ 0 Empty (k + 1) :=
  Rew.bind Fin.elim0 (fun j ↦ .bvar (finiteVariableIndex k j))

def finiteVariableRew (k : ℕ) : (n : ℕ) → Rew ℒₛₑₜ ℕ n Empty ((k + 1) + n)
  | 0 => finiteVariableBase k
  | n + 1 => (finiteVariableRew k n).q

def finiteVariableClosure (k : ℕ) {n : ℕ} (φ : SetTheorySemiproposition n) :
    SetTheorySemisentence ((k + 1) + n) := (finiteVariableRew k n) ▹ φ

@[simp] theorem finiteVariableClosure_verum (k n : ℕ) :
    finiteVariableClosure k (⊤ : SetTheorySemiproposition n) = ⊤ := rfl

@[simp] theorem finiteVariableClosure_falsum (k n : ℕ) :
    finiteVariableClosure k (⊥ : SetTheorySemiproposition n) = ⊥ := rfl

@[simp] theorem finiteVariableClosure_neg (k : ℕ) {n : ℕ} (φ : SetTheorySemiproposition n) :
    finiteVariableClosure k (∼φ) = ∼finiteVariableClosure k φ := by
  simp [finiteVariableClosure]

@[simp] theorem finiteVariableClosure_and (k : ℕ) {n : ℕ} (φ ψ : SetTheorySemiproposition n) :
    finiteVariableClosure k (φ ⋏ ψ) = finiteVariableClosure k φ ⋏ finiteVariableClosure k ψ := rfl

@[simp] theorem finiteVariableClosure_or (k : ℕ) {n : ℕ} (φ ψ : SetTheorySemiproposition n) :
    finiteVariableClosure k (φ ⋎ ψ) = finiteVariableClosure k φ ⋎ finiteVariableClosure k ψ := rfl

@[simp] theorem finiteVariableClosure_all (k : ℕ) {n : ℕ} (φ : SetTheorySemiproposition (n + 1)) :
    finiteVariableClosure (n := n) k (∀¹ φ) = ∀¹ finiteVariableClosure (n := n + 1) k φ := rfl

@[simp] theorem finiteVariableClosure_exs (k : ℕ) {n : ℕ} (φ : SetTheorySemiproposition (n + 1)) :
    finiteVariableClosure (n := n) k (∃¹ φ) = ∃¹ finiteVariableClosure (n := n + 1) k φ := rfl

theorem finiteVariableClosure_free (k : ℕ) (φ : SetTheorySemiproposition 1) :
    finiteVariableClosure (k + 1) φ.free = finiteVariableClosure k φ := by
  have hr : (finiteVariableBase (k + 1)).comp Rew.free = (finiteVariableBase k).q := by
    apply Rew.ext
    · intro i
      refine Fin.cases ?_ (fun j ↦ Fin.elim0 j) i
      simp [Rew.comp_app, finiteVariableBase, finiteVariableIndex]
    · intro j
      simp [Rew.comp_app, finiteVariableBase, finiteVariableIndex, Nat.add_min_add_right]
  change (finiteVariableBase (k + 1)) ▹ Rew.free ▹ φ = (finiteVariableBase k).q ▹ φ
  rw [← TransitiveRewriting.comp_app, hr]

theorem finiteVariableClosure_shift (k : ℕ) (φ : SetTheoryProposition) :
    finiteVariableClosure (k + 1) φ.shift = Rew.bShift ▹ finiteVariableClosure k φ := by
  have hr : (finiteVariableBase (k + 1)).comp Rew.shift = Rew.bShift.comp (finiteVariableBase k) := by
    apply Rew.ext
    · intro i
      exact Fin.elim0 i
    · intro j
      simp [Rew.comp_app, finiteVariableBase, finiteVariableIndex, Nat.add_min_add_right]
  change (finiteVariableBase (k + 1)) ▹ Rew.shift ▹ φ = Rew.bShift ▹ (finiteVariableBase k) ▹ φ
  rw [← TransitiveRewriting.comp_app, hr, TransitiveRewriting.comp_app]

def instantiateBoundRew {n : ℕ} (i : Fin n) : Rew ℒₛₑₜ Empty (n + 1) Empty n :=
  Rew.bind (Fin.cons (.bvar i) Semiterm.bvar) Empty.elim

theorem finiteVariableClosure_subst (k j : ℕ) (φ : SetTheorySemiproposition 1) :
    finiteVariableClosure (n := 0) k (φ/[Semiterm.fvar j]) =
      instantiateBoundRew (finiteVariableIndex k j) ▹ finiteVariableClosure k φ := by
  have hr : (finiteVariableBase k).comp (Rew.subst ![Semiterm.fvar j]) =
      (instantiateBoundRew (finiteVariableIndex k j)).comp (finiteVariableBase k).q := by
    apply Rew.ext
    · intro i
      refine Fin.cases ?_ (fun t ↦ Fin.elim0 t) i
      simp [Rew.comp_app, finiteVariableBase, instantiateBoundRew]
    · intro i
      simp [Rew.comp_app, finiteVariableBase, instantiateBoundRew]
  change (finiteVariableBase k) ▹ (Rew.subst ![Semiterm.fvar j]) ▹ φ =
    (instantiateBoundRew (finiteVariableIndex k j)) ▹ (finiteVariableBase k).q ▹ φ
  rw [← TransitiveRewriting.comp_app, hr, TransitiveRewriting.comp_app]

theorem finiteVariableClosure_embed (k : ℕ) (φ : SetTheorySentence)
    (σ : Rew ℒₛₑₜ Empty 0 Empty (k + 1)) :
    finiteVariableClosure k (φ : SetTheoryProposition) = σ ▹ φ := by
  have hr : (finiteVariableBase k).comp Rew.emb = σ := by
    apply Rew.ext
    · intro i; exact Fin.elim0 i
    · intro i; exact Empty.elim i
  change (finiteVariableBase k) ▹ Rew.emb ▹ φ = σ ▹ φ
  rw [← TransitiveRewriting.comp_app, hr]

end ZFVP
