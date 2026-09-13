import ZFVP.SetTheory.UniformLevyForcing
import ZFVP.SetTheory.PiTwoDependentChoice
import ZFVP.SetTheory.DeltaOneCheckNames
import ZFVP.ModelTheory.ForcingConditionalEquivalence
import ZFVP.ModelTheory.ForcingCheckedBounded
import ZFVP.ModelTheory.WoodinCollapseForcesRestoration

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def checkedLevyForcingFormula (θ : SetTheorySemisentence 4) : SetTheorySemisentence 5 :=
  “P R one p κ. ∀ τ, !(sigmaOneCheckNameFormula true) one κ τ → !θ P R p τ”

theorem checkedLevyForcingFormula_piTwo {θ : SetTheorySemisentence 4}
    (hθ : IsPiFormula 2 θ) : IsPiFormula 2 (checkedLevyForcingFormula θ) :=
  .all (.or (.raise ((sigmaOneCheckNameFormula_sigmaOne true).subst _).neg)
    (hθ.subst _))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_checkedLevyForcingFormula (θ : SetTheorySemisentence 4) (P R one p κ : V) :
    (checkedLevyForcingFormula θ).Evalb ![P, R, one, p, κ] ↔
      θ.Evalb ![P, R, p, checkName one κ] := by
  simp [checkedLevyForcingFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, eval_sigmaOneCheckNameFormula, TruthAnswer]

theorem forcing_piTwoDependentChoiceBelow_iff {P R one p κ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hp : p ∈ P) (hκ : IsOrdinal κ) :
    p ∈ forcingFormula P R piTwoOrdinalDependentChoiceBelowFormula
      (standardTuple ![checkName one κ]) ↔
    p ∈ forcingFormula P R dependentChoiceBelowFormula
      (standardTuple ![checkName one κ]) := by
  let c : ForcingName P := ⟨checkName one κ, checkName_isName htop.1 κ⟩
  apply forcingFormula_iff_under IsOrdinal.dfn piTwoOrdinalDependentChoiceBelowFormula
    dependentChoiceBelowFormula (fun W _ _ _ v hv ↦ ?_) hR htop hp ![c]
    (forces_checked_ordinal hR htop hκ hp)
  have hk : IsOrdinal (v 0) := (Defined.eval_iff v).mp hv
  simp only [Defined.eval_iff]
  exact and_iff_right hk

theorem forcing_dependentChoiceBelow_piTwo_uniform :
    ∃ Ψ : SetTheorySemisentence 5, IsPiFormula 2 Ψ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ P R one p κ : V, IsForcingPreorder P R → IsForcingTop P R one →
          p ∈ P → IsOrdinal κ →
          (Ψ.Evalb ![P, R, one, p, κ] ↔ p ∈ forcingFormula P R dependentChoiceBelowFormula
            (standardTuple ![checkName one κ])) := by
  obtain ⟨θ, hθ, he⟩ := IsLevyFormula.ordinaryForcing_definition_uniform.{u}
    piTwoOrdinalDependentChoiceBelowFormula_piTwo (by omega)
  refine ⟨checkedLevyForcingFormula θ, checkedLevyForcingFormula_piTwo hθ, ?_⟩
  intro V _ _ _ P R one p κ hR ht hp hk
  rw [eval_checkedLevyForcingFormula]
  exact (he V P R hR ![checkName one κ]
    (by intro i; exact Fin.cases (checkName_isName ht.1 κ) (fun j ↦ Fin.elim0 j) i) p).trans
    (forcing_piTwoDependentChoiceBelow_iff hR ht hp hk)

end ZFVP
