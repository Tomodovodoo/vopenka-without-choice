import ZFVP.SetTheory.CorrectRankStages
import ZFVP.SetTheory.PiOneHierarchy

/-! Pi_n definitions of recursively correct rank stages for n at least two. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def piCorrectRankStageFormula (k : ℕ) : SetTheorySemisentence 1 :=
  “α. !IsOrdinal.dfn α ∧ ∀ A, !piOneHierarchyFormula A α → !(correctDomainFormula k) A”

theorem piCorrectRankStageFormula_bound (k : ℕ) :
    IsPiFormula (max 2 k) (piCorrectRankStageFormula k) := by
  generalize he : max 2 k = l
  have h2 : 2 ≤ l := he ▸ Nat.le_max_left 2 k
  have hk : k ≤ l := he ▸ Nat.le_max_right 2 k
  cases l with
  | zero => omega
  | succ l =>
    refine .and (.bounded (isOrdinalFormula_bounded.subst _)) (.all (.or ?_ ?_))
    · exact (IsLevyFormula.raise (piOneHierarchyFormula_piOne.subst _).neg).mono h2
    · exact ((correctDomainFormula_pi k).mono hk).subst _

theorem piCorrectRankStageFormula_pi {k : ℕ} (hk : 2 ≤ k) :
    IsPiFormula k (piCorrectRankStageFormula k) := by
  simpa only [Nat.max_eq_right hk] using piCorrectRankStageFormula_bound k

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_piCorrectRankStageFormula (k : ℕ) (α : V) :
    (piCorrectRankStageFormula k).Evalb ![α] ↔ IsCorrectRankStage k α := by
  simp (config := { contextual := true }) [piCorrectRankStageFormula, IsHierarchySegment, IsCorrectRankStage]

instance piCorrectRankStageFormula_defined (k : ℕ) :
    ℒₛₑₜ-predicate[V] (IsCorrectRankStage k) via piCorrectRankStageFormula k :=
  ⟨fun (v : Fin 1 → V) ↦ by
    have hv : ![v 0] = v := by funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
    change (piCorrectRankStageFormula k).Evalb v ↔ IsCorrectRankStage k (v 0)
    rw [← hv]
    exact eval_piCorrectRankStageFormula k (v 0)⟩

end ZFVP
