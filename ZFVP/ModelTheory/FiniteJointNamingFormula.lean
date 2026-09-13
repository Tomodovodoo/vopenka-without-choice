import Foundation.FirstOrder.SetTheory.ZF

/-! A first-order formula for a finite tuple subject to a formula, prescribed
parameter values, and equalities with an outer tuple. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {M : Type*} [SetStructure M]

def finiteSourceNameGuard {N p : ℕ} (source : Fin N → Option M) : SetTheorySemiformula M (p + N) :=
  Matrix.conj fun t ↦ match source t with
    | none => ⊤
    | some x => “#(t.addCast p) = &x”

def finiteUpperNameGuard {N p : ℕ} (slot : Fin p → Option (Fin N)) : SetTheorySemiformula M (p + N) :=
  Matrix.conj fun t ↦ match slot t with
    | none => ⊤
    | some s => “#(s.addCast p) = #(t.addNat N)”

def finiteJointNamingFormula {N p : ℕ} (ψ : SetTheorySemisentence N)
    (source : Fin N → Option M) (slot : Fin p → Option (Fin N)) : SetTheorySemiformula M p :=
  ∃¹^[N] (((Rew.embSubsts (fun t : Fin N ↦ #(t.addCast p))) ▹ ψ) ⋏
    finiteSourceNameGuard source ⋏ finiteUpperNameGuard slot)

theorem eval_finiteSourceNameGuard {N p : ℕ} (source : Fin N → Option M)
    (a : Fin N → M) (u : Fin p → M) :
    Semiformula.Eval (Matrix.appendr a u) id (finiteSourceNameGuard source) ↔
      ∀ t x, source t = some x → a t = x := by
  rw [finiteSourceNameGuard, Matrix.conj_hom_prop]
  apply forall_congr'
  intro t
  cases hs : source t <;> simp

theorem eval_finiteUpperNameGuard {N p : ℕ} (slot : Fin p → Option (Fin N))
    (a : Fin N → M) (u : Fin p → M) :
    Semiformula.Eval (Matrix.appendr a u) id (finiteUpperNameGuard slot) ↔
      ∀ t s, slot t = some s → a s = u t := by
  rw [finiteUpperNameGuard, Matrix.conj_hom_prop]
  apply forall_congr'
  intro t
  cases hs : slot t <;> simp

theorem eval_finiteJointNamingFormula {N p : ℕ} (ψ : SetTheorySemisentence N)
    (source : Fin N → Option M) (slot : Fin p → Option (Fin N)) (u : Fin p → M) :
    Semiformula.Eval u id (finiteJointNamingFormula ψ source slot) ↔
      ∃ a : Fin N → M, ψ.Evalb a ∧
        (∀ t x, source t = some x → a t = x) ∧
        ∀ t s, slot t = some s → a s = u t := by
  rw [finiteJointNamingFormula, Semiformula.eval_exsItr]
  apply exists_congr
  intro a
  simp only [LogicalConnective.HomClass.map_and, eval_finiteSourceNameGuard,
    eval_finiteUpperNameGuard, Semiformula.eval_embSubsts, Function.comp_def,
    Semiterm.val_bvar, Matrix.appeendr_addCast]
  rfl

end ZFVP
