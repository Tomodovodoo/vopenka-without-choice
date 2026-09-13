import ZFVP.Syntax.CloseParameters
import ZFVP.Syntax.TemplateInstantiation

/-! Closing free parameters in the index order used by the schema templates. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def closeTailParameters {n : ℕ} (φ : SetTheorySemiproposition (n + 1)) :
    SetTheorySemisentence (φ.fvSup + (n + 1)) :=
  (Rew.bind (fun i ↦ .bvar (Fin.castLE (Nat.le_add_left (n + 1) φ.fvSup) i))
    (fun j ↦ if h : j < φ.fvSup then .bvar (Fin.addNat ⟨j, h⟩ (n + 1))
      else .bvar 0)) ▹ φ

theorem eval_closeTailParameters {M : Type*} [SetStructure M] [Nonempty M]
    {n : ℕ} (φ : SetTheorySemiproposition (n + 1)) (b : Fin (n + 1) → M) (e : ℕ → M) :
    (closeTailParameters φ).Evalb (prefixVector b (fun i : Fin φ.fvSup ↦ e i.val)) ↔ φ.Eval b e := by
  unfold closeTailParameters Semiformula.Evalb
  rw [Semiformula.eval_rew]
  have hb : (Semiterm.val (L := ℒₛₑₜ) (prefixVector b (fun i : Fin φ.fvSup ↦ e i.val)) Empty.elim ∘
      (Rew.bind (fun i : Fin (n + 1) ↦ .bvar (Fin.castLE (Nat.le_add_left (n + 1) φ.fvSup) i))
        (fun j ↦ if h : j < φ.fvSup then .bvar (Fin.addNat ⟨j, h⟩ (n + 1)) else .bvar 0)) ∘
      Semiterm.bvar) = b := by
    funext i
    simp [prefixVector_front]
  rw [hb]
  apply Semiformula.eval_iff_of_funEqOn
  intro j hj
  simpa [Semiformula.lt_fvSup_of_fvar? hj] using
    (prefixVector_tail b (fun i : Fin φ.fvSup ↦ e i.val)
      ⟨j, Semiformula.lt_fvSup_of_fvar? hj⟩)

end ZFVP
