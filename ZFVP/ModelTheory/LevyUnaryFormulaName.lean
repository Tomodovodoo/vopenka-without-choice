import ZFVP.SetTheory.LevyForcingUniqueName
import ZFVP.SetTheory.UniformLevyForcing
import ZFVP.ModelTheory.ForcingNameNormalization
import ZFVP.ModelTheory.ForcingReverseOrderName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def unaryNameOutputFormula (θ : SetTheorySemisentence 5) : SetTheorySemisentence 5 :=
  θ.subst ![.bvar 0, .bvar 1, .bvar 4, .bvar 3, .bvar 2]

theorem unaryFormulaName_sigma_uniform {k : ℕ} (φ : SetTheorySemisentence 2)
    (hφ : IsSigmaFormula (k + 1) φ) :
    ∃ Λ : SetTheorySemisentence 4, IsSigmaFormula (k + 2) Λ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ N P R τ : V, IsForcingPreorder P R → IsForcingName P τ →
          (Λ.Evalb ![N, P, R, τ] ↔ N = formulaUniqueName P R φ (standardTuple ![τ])) := by
  obtain ⟨θ, hθ, he⟩ := IsLevyFormula.ordinaryForcing_definition_uniform.{u} hφ (by omega)
  refine ⟨levyUniqueNameGraphFormula (unaryNameOutputFormula θ),
    levyUniqueNameGraphFormula_sigma (hθ.subst _), ?_⟩
  intro V _ _ _ N P R τ hR hτ
  apply eval_levyUniqueNameGraphFormula _ N P R τ (standardTuple ![τ])
    (fun b ν ↦ forcingFormula P R φ (assignmentPrepend (1 : V) b ν)) (by definability)
  intro ν hν p
  have hnames : ∀ i : Fin 2, IsForcingName P ((![ν, τ] : Fin 2 → V) i) := by
    intro i
    exact Fin.cases hν (fun j ↦ Fin.cases hτ (fun t ↦ Fin.elim0 t) j) i
  have ho := he V P R hR ![ν, τ] hnames p
  have ht : (unaryNameOutputFormula θ).Evalb ![P, R, τ, ν, p] ↔
      θ.Evalb ![P, R, p, ν, τ] := by
    simp [unaryNameOutputFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [ht]
  exact ho

def uniqueNamePiGraph (Λ : SetTheorySemisentence 4) : SetTheorySemisentence 4 :=
  “N P R τ. ∀ M, !Λ M P R τ → M = N”

theorem uniqueNamePiGraph_pi {k : ℕ} {Λ : SetTheorySemisentence 4}
    (hΛ : IsSigmaFormula (k + 1) Λ) : IsPiFormula (k + 1) (uniqueNamePiGraph Λ) :=
  .all (.or (hΛ.subst _).neg (.bounded (.rel _ _)))

theorem unaryFormulaName_delta_uniform {k : ℕ} (φ : SetTheorySemisentence 2)
    (hφ : IsSigmaFormula (k + 1) φ) :
    ∃ Λ Ξ : SetTheorySemisentence 4, IsSigmaFormula (k + 2) Λ ∧ IsPiFormula (k + 2) Ξ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ N P R τ : V, IsForcingPreorder P R → IsForcingName P τ →
          (Λ.Evalb ![N, P, R, τ] ↔ N = formulaUniqueName P R φ (standardTuple ![τ])) ∧
          (Ξ.Evalb ![N, P, R, τ] ↔ N = formulaUniqueName P R φ (standardTuple ![τ])) := by
  obtain ⟨Λ, hΛ, he⟩ := unaryFormulaName_sigma_uniform.{u} φ hφ
  refine ⟨Λ, uniqueNamePiGraph Λ, hΛ, uniqueNamePiGraph_pi hΛ, ?_⟩
  intro V _ _ _ N P R τ hR hτ
  refine ⟨he V N P R τ hR hτ, ?_⟩
  have ht : (uniqueNamePiGraph Λ).Evalb ![N, P, R, τ] ↔
      ∀ M : V, Λ.Evalb ![M, P, R, τ] → M = N := by
    simp [uniqueNamePiGraph, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [ht]
  simp only [he V _ P R τ hR hτ]
  simp [eq_comm]

theorem forcingRankName_deltaTwo_uniform :
    ∃ Λ Ξ : SetTheorySemisentence 4, IsSigmaFormula 2 Λ ∧ IsPiFormula 2 Ξ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ N P R τ : V, IsForcingPreorder P R → IsForcingName P τ →
          (Λ.Evalb ![N, P, R, τ] ↔ N = forcingRankName P R τ) ∧
          (Ξ.Evalb ![N, P, R, τ] ↔ N = forcingRankName P R τ) :=
  unaryFormulaName_delta_uniform sigmaOneRankFormula sigmaOneRankFormula_sigmaOne

theorem reverseInclusionOrderName_deltaThree_uniform :
    ∃ Λ Ξ : SetTheorySemisentence 4, IsSigmaFormula 3 Λ ∧ IsPiFormula 3 Ξ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ N P R Q : V, IsForcingPreorder P R → IsForcingName P Q →
          (Λ.Evalb ![N, P, R, Q] ↔ N = reverseInclusionOrderName P R Q) ∧
          (Ξ.Evalb ![N, P, R, Q] ↔ N = reverseInclusionOrderName P R Q) :=
  unaryFormulaName_delta_uniform piOneReverseInclusionOrderFormula piOneReverseInclusionOrderFormula_piOne.raise

end ZFVP


