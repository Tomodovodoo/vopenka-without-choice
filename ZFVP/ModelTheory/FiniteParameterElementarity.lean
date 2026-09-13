import Foundation.FirstOrder.Basic.Semantics.Semantics
import Mathlib.Data.Fintype.EquivFin

/-! Preservation of finite bound-variable formulas implies preservation with arbitrary free parameters. -/

namespace ZFVP

open LO LO.FirstOrder

theorem elementary_of_semisentences {L : Language} {M N : Type*}
    [Structure L M] [Structure L N] [Nonempty M] (j : M → N)
    (hj : ∀ {n : ℕ} (φ : Semisentence L n) (b : Fin n → M),
      φ.Evalb b ↔ φ.Evalb (j ∘ b))
    {ξ : Type*} {n : ℕ} (φ : Semiformula L ξ n) (b : Fin n → M) (a : ξ → M) :
    φ.Eval b a ↔ φ.Eval (j ∘ b) (j ∘ a) := by
  classical
  let S := φ.freeVariables
  let k := Fintype.card {x // x ∈ S}
  let e : {x // x ∈ S} ≃ Fin k := Fintype.equivFin _
  let ix : ξ → Fin (k + 1) := fun x ↦ if h : x ∈ S then (e ⟨x, h⟩).succ else 0
  let ρ : Rew L ξ n Empty (n + (k + 1)) :=
    Rew.bind (fun i ↦ .bvar (Fin.castAdd (k + 1) i)) (fun x ↦ .bvar (Fin.natAdd n (ix x)))
  let c : Fin (n + (k + 1)) → M := Fin.append b
    (Fin.cases (Classical.choice ‹Nonempty M›) (fun i ↦ a (e.symm i).val))
  have hcb (i : Fin n) : c (Fin.castAdd (k + 1) i) = b i := by simp [c]
  have hca (x : ξ) (hx : φ.FVar? x) : c (Fin.natAdd n (ix x)) = a x := by
    have hxS : x ∈ S := hx
    simp [c, ix, hxS]
  have hs : (ρ ▹ φ).Evalb c ↔ φ.Eval b a := by
    rw [Semiformula.eval_rew]
    have hb : (Semiterm.val c Empty.elim ∘ ρ ∘ Semiterm.bvar) = b := by
      funext i
      simpa [ρ, Function.comp_def] using hcb i
    rw [hb]
    apply Semiformula.eval_iff_of_funEqOn
    intro x hx
    simpa [ρ, Function.comp_def] using hca x hx
  have ht : (ρ ▹ φ).Evalb (j ∘ c) ↔ φ.Eval (j ∘ b) (j ∘ a) := by
    rw [Semiformula.eval_rew]
    have hb : (Semiterm.val (j ∘ c) Empty.elim ∘ ρ ∘ Semiterm.bvar) = j ∘ b := by
      funext i
      simpa [ρ, Function.comp_def] using congrArg j (hcb i)
    rw [hb]
    apply Semiformula.eval_iff_of_funEqOn
    intro x hx
    simpa [ρ, Function.comp_def] using congrArg j (hca x hx)
  exact hs.symm.trans ((hj (ρ ▹ φ) c).trans ht)

end ZFVP
