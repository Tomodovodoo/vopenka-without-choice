import ZFVP.ModelTheory.LevyBinaryFormulaName
import ZFVP.SetTheory.SigmaTwoWoodinCollapse
import ZFVP.ModelTheory.WoodinCollapseName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def sigmaTwoTotalWoodinCollapseFormula : SetTheorySemisentence 3 :=
  “Q κ δ. !sigmaTwoWoodinCollapseFormula Q κ δ ∨ (¬!IsOrdinal.dfn δ ∧ !boundedEmptyFormula Q)”

theorem sigmaTwoTotalWoodinCollapseFormula_sigmaTwo : IsSigmaFormula 2 sigmaTwoTotalWoodinCollapseFormula :=
  .or (sigmaTwoWoodinCollapseFormula_sigmaTwo.subst _)
    (.bounded (.and (isOrdinalFormula_bounded.subst _).neg (boundedEmptyFormula_bounded.subst _)))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaTwoTotalWoodinCollapseFormula (Q κ δ : V) :
    sigmaTwoTotalWoodinCollapseFormula.Evalb ![Q, κ, δ] ↔ Q = totalWoodinCollapse κ δ := by
  classical
  by_cases hd : IsOrdinal δ <;>
    simp [sigmaTwoTotalWoodinCollapseFormula, eval_sigmaTwoWoodinCollapseFormula, totalWoodinCollapse, hd,
      Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]

theorem woodinCollapseName_sigmaThree_uniform :
    ∃ Λ : SetTheorySemisentence 5, IsSigmaFormula 3 Λ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ N P R one κ δ : V, IsForcingPreorder P R → IsForcingTop P R one →
          IsForcingName P κ → IsForcingName P δ →
          (Λ.Evalb ![N, P, R, κ, δ] ↔ N = woodinCollapseName P R κ δ) := by
  have hv : ∀ (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
      ∀ v : Fin 3 → W, sigmaTwoTotalWoodinCollapseFormula.Evalb v ↔ totalWoodinCollapseFormula.Evalb v := by
    intro W _ _ _ v
    have hv : ![v 0, v 1, v 2] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.cases rfl (fun e ↦ Fin.elim0 e) t) j) i
    rw [← hv]
    have hf : totalWoodinCollapseFormula.Evalb ![v 0, v 1, v 2] ↔ v 0 = totalWoodinCollapse (v 1) (v 2) :=
      (totalWoodinCollapseFormula_defined (V := W)).iff ![v 0, v 1, v 2]
    exact (eval_sigmaTwoTotalWoodinCollapseFormula _ _ _).trans hf.symm
  obtain ⟨Λ, hΛ, he⟩ := binaryFormulaName_sigma_uniform_of_equiv (k := 1)
    totalWoodinCollapseFormula sigmaTwoTotalWoodinCollapseFormula sigmaTwoTotalWoodinCollapseFormula_sigmaTwo hv
  refine ⟨Λ, hΛ, ?_⟩
  intro W _ _ _ N P R one κ δ hR ht hκ hδ
  exact he W N P R one κ δ hR ht hκ hδ

end ZFVP
