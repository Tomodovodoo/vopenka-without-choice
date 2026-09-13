import ZFVP.Syntax.MembershipSatisfaction

/-! Closing the finitely many free parameters of an external formula. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def closeParameters {n : ℕ} (φ : SetTheorySemiproposition (n + 1)) :
    SetTheorySemisentence ((n + 1) + φ.fvSup) :=
  (Rew.bind (fun i ↦ .bvar (i.castAdd φ.fvSup))
    (fun j ↦ if h : j < φ.fvSup then .bvar (Fin.natAdd (n + 1) ⟨j, h⟩)
      else .bvar 0)) ▹ φ

theorem eval_closeParameters {M : Type*} [Structure ℒₛₑₜ M] [Nonempty M]
    {n : ℕ} (φ : SetTheorySemiproposition (n + 1))
    (b : Fin (n + 1) → M) (e : ℕ → M) :
    (closeParameters φ).Evalb (Fin.append b (fun i : Fin φ.fvSup ↦ e i.val)) ↔
      φ.Eval b e := by
  unfold closeParameters Semiformula.Evalb
  rw [Semiformula.eval_rew]
  have hb : (Semiterm.val (L := ℒₛₑₜ) (Fin.append b (fun i : Fin φ.fvSup ↦ e i.val)) Empty.elim ∘
      (Rew.bind (fun i : Fin (n + 1) ↦ .bvar (i.castAdd φ.fvSup))
        (fun j ↦ if h : j < φ.fvSup then .bvar (Fin.natAdd (n + 1) ⟨j, h⟩)
          else .bvar 0)) ∘ Semiterm.bvar) = b := by
    funext i
    simp
  rw [hb]
  apply Semiformula.eval_iff_of_funEqOn
  intro j hj
  simpa [Semiformula.lt_fvSup_of_fvar? hj] using
    (Fin.append_right b (fun i : Fin φ.fvSup ↦ e i.val)
      ⟨j, Semiformula.lt_fvSup_of_fvar? hj⟩)

end ZFVP
