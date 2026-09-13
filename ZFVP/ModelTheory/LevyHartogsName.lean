import ZFVP.ModelTheory.LevyEquivalentUnaryName
import ZFVP.ModelTheory.ForcingHartogsName
import ZFVP.SetTheory.DeltaTwoHartogs

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

theorem hartogsNumberName_sigmaThree_uniform :
    ∃ Λ : SetTheorySemisentence 4, IsSigmaFormula 3 Λ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ N P R one τ : V, IsForcingPreorder P R → IsForcingTop P R one → IsForcingName P τ →
          (Λ.Evalb ![N, P, R, τ] ↔ N = hartogsNumberName P R τ) := by
  have hv : ∀ (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
      ∀ b : Fin 2 → W, deltaTwoHartogsFormula.Evalb b ↔ hartogsNumberFormula.Evalb b := by
    intro W _ _ _ b
    exact (deltaTwoHartogsFormula_defined.iff b).trans (hartogsNumberFormula_defined.iff b).symm
  obtain ⟨Λ, hΛ, he⟩ := unaryFormulaName_sigma_uniform_of_equiv (k := 1)
    hartogsNumberFormula deltaTwoHartogsFormula (deltaTwoHartogsFormula_levy .sigma) hv
  refine ⟨Λ, hΛ, ?_⟩
  intro W _ _ _ N P R one τ hR ht hτ
  exact he W N P R one τ hR ht hτ

theorem hartogsNumberName_deltaThree_uniform :
    ∃ Λ Ξ : SetTheorySemisentence 4, IsSigmaFormula 3 Λ ∧ IsPiFormula 3 Ξ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ N P R one τ : V, IsForcingPreorder P R → IsForcingTop P R one → IsForcingName P τ →
          (Λ.Evalb ![N, P, R, τ] ↔ N = hartogsNumberName P R τ) ∧
          (Ξ.Evalb ![N, P, R, τ] ↔ N = hartogsNumberName P R τ) := by
  obtain ⟨Λ, hΛ, he⟩ := hartogsNumberName_sigmaThree_uniform.{u}
  refine ⟨Λ, uniqueNamePiGraph Λ, hΛ, uniqueNamePiGraph_pi hΛ, ?_⟩
  intro W _ _ _ N P R one τ hR ht hτ
  refine ⟨he W N P R one τ hR ht hτ, ?_⟩
  have hb : (uniqueNamePiGraph Λ).Evalb ![N, P, R, τ] ↔
      ∀ M : W, Λ.Evalb ![M, P, R, τ] → M = N := by
    simp [uniqueNamePiGraph, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [hb]
  simp only [he W _ P R one τ hR ht hτ]
  simp [eq_comm]

end ZFVP
