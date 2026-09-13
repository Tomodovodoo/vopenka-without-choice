import ZFVP.SetTheory.Cn

/-! In ZF, C(1) has both Sigma-two and Pi-two definitions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaTwoCnOneFormula : SetTheorySemisentence 1 :=
  “α. ∃ A, !piOneHierarchyFormula A α ∧ !(correctDomainFormula 1) A”

theorem sigmaTwoCnOneFormula_sigmaTwo : IsSigmaFormula 2 sigmaTwoCnOneFormula :=
  .exs (.and (piOneHierarchyFormula_piOne.subst _).raise ((correctDomainFormula_pi 1).subst _).raise)

theorem cnOneFormula_piTwo : IsPiFormula 2 (cnFormula 1) := cnFormula_pi_bound 1

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaTwoCnOneFormula (α : V) : sigmaTwoCnOneFormula.Evalb ![α] ↔ Cn 1 α := by
  simp [sigmaTwoCnOneFormula, IsHierarchySegment, cn_successor_iff, IsCorrectRankStage]

instance sigmaTwoCnOneFormula_defined : ℒₛₑₜ-predicate[V] (Cn 1) via sigmaTwoCnOneFormula :=
  ⟨fun (v : Fin 1 → V) ↦ by
    have hv : ![v 0] = v := by funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
    change sigmaTwoCnOneFormula.Evalb v ↔ Cn 1 (v 0)
    rw [← hv]
    exact eval_sigmaTwoCnOneFormula (v 0)⟩

theorem cnOne_deltaTwo :
    IsSigmaFormula 2 sigmaTwoCnOneFormula ∧ IsPiFormula 2 (cnFormula 1) ∧
      ∀ α : V, (sigmaTwoCnOneFormula.Evalb ![α] ↔ Cn 1 α) ∧ ((cnFormula 1).Evalb ![α] ↔ Cn 1 α) :=
  ⟨sigmaTwoCnOneFormula_sigmaTwo, cnOneFormula_piTwo, fun α ↦
    ⟨eval_sigmaTwoCnOneFormula α, eval_cnFormula 1 α⟩⟩

theorem Cn.cnOne_sigma_absolute {k : ℕ} {δ : V} (hδ : Cn (k + 2) δ)
    (α : SetDomain (hierarchy δ)) : sigmaTwoCnOneFormula.Evalb ![α] ↔ Cn 1 α.val := by
  have he := hδ.sigma_correct (sigmaTwoCnOneFormula_sigmaTwo.mono (by omega)) ![α]
  have hv : (fun i : Fin 1 ↦ (![α] i).val) = ![α.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  rw [hv] at he
  exact he.trans (eval_sigmaTwoCnOneFormula α.val)

end ZFVP
