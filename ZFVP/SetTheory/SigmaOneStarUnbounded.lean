import ZFVP.SetTheory.SigmaOneStarCorrectness
import ZFVP.SetTheory.CnAbsoluteness
import ZFVP.SetTheory.LevyComplexityBound

/-! The strengthened Sigma-one-correct ranks are unbounded. A single
finite correctness bound suffices for their internal witness predicate. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def starReflectionExistsFormula : SetTheorySemisentence 3 :=
  “α φ a. ∃ b, !starReflectionWitnessFormula α φ a b”

theorem starReflectionExistsFormula_complexity {n : ℕ}
    (h : IsLevyFormula .sigma (n + 1) starReflectionWitnessFormula) :
    IsLevyFormula .sigma (n + 2) starReflectionExistsFormula :=
  .exs (h.raise.subst _)

theorem eval_starReflectionExists_components {W : Type*} [SetStructure W] (α φ a : W) :
    starReflectionExistsFormula.Evalb ![α, φ, a] ↔
      ∃ b, starReflectionWitnessFormula.Evalb ![α, φ, a, b] := by
  simp [starReflectionExistsFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Function.comp_def, Matrix.constant_eq_singleton]

private theorem positiveStarComplexity {m : ℕ} (φ : SetTheorySemisentence m) :
    IsLevyFormula .sigma (levySyntacticBound φ + 1) φ :=
  (isLevyFormula_syntacticBound φ .sigma).raise

opaque starReflectionComplexity :
    {n : ℕ // IsLevyFormula .sigma (n + 1) starReflectionWitnessFormula} :=
  ⟨levySyntacticBound starReflectionWitnessFormula,
    positiveStarComplexity starReflectionWitnessFormula⟩

def sigmaOneStarCorrectnessBound : ℕ := starReflectionComplexity.val + 2

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem Cn.sigmaOneStarCorrect_of_complexity {n : ℕ} {γ : V}
    (hγ : Cn (n + 2) γ)
    (hW : IsLevyFormula .sigma (n + 1) starReflectionWitnessFormula) :
    IsSigmaOneStarCorrect γ := by
  let := hγ.ordinal
  let : IsSequenceSupport (hierarchy γ) := ((cn_successor_iff (n + 1) γ).mp hγ).2.support
  refine ⟨hγ.of_le (by omega), ?_⟩
  intro α hα a ha φ hφ hex
  let aa : SetDomain (hierarchy γ) := ⟨α, ordinal_subset_hierarchy γ α hα⟩
  let xx : SetDomain (hierarchy γ) := ⟨a, ha⟩
  let pp : SetDomain (hierarchy γ) := ⟨φ, boundedFormulaCode_formula_mem_support hφ⟩
  have hg : starReflectionExistsFormula.Evalb ![α, φ, a] := by
    rw [eval_starReflectionExists_components]
    simpa using hex
  have he := hγ.sigma_correct (starReflectionExistsFormula_complexity hW) ![aa, pp, xx]
  have hv : (fun i : Fin 3 ↦ (![aa, pp, xx] i).val) = ![α, φ, a] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i
  rw [hv] at he
  obtain ⟨b, hb⟩ := (eval_starReflectionExists_components aa pp xx).mp (he.mpr hg)
  refine ⟨b.val, b.property, ?_⟩
  exact (hγ.defined_correct (hW.raise (q := .sigma))
    (fun v ↦ StarReflectionWitness (v 0) (v 1) (v 2) (v 3)) ![aa, pp, xx, b]).mp hb

theorem Cn.sigmaOneStarCorrect {γ : V} (hγ : Cn sigmaOneStarCorrectnessBound γ) :
    IsSigmaOneStarCorrect γ :=
  Cn.sigmaOneStarCorrect_of_complexity (n := starReflectionComplexity.val)
    hγ starReflectionComplexity.property

theorem sigmaOneStarCorrect_unbounded (α : V) [IsOrdinal α] :
    ∃ γ : V, α ∈ γ ∧ IsSigmaOneStarCorrect γ := by
  obtain ⟨γ, hαγ, hγ⟩ := cn_unbounded sigmaOneStarCorrectnessBound α
  exact ⟨γ, hαγ, hγ.sigmaOneStarCorrect⟩

end ZFVP
