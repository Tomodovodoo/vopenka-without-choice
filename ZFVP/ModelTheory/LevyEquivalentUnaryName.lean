import ZFVP.ModelTheory.LevyUnaryFormulaName
import ZFVP.ModelTheory.ForcingEntailment

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

theorem unaryFormulaName_sigma_uniform_of_equiv {k : ℕ} (φ χ : SetTheorySemisentence 2)
    (hχ : IsSigmaFormula (k + 1) χ)
    (hv : ∀ (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
      ∀ b : Fin 2 → W, χ.Evalb b ↔ φ.Evalb b) :
    ∃ Λ : SetTheorySemisentence 4, IsSigmaFormula (k + 2) Λ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ N P R one τ : V, IsForcingPreorder P R → IsForcingTop P R one → IsForcingName P τ →
          (Λ.Evalb ![N, P, R, τ] ↔ N = formulaUniqueName P R φ (standardTuple ![τ])) := by
  obtain ⟨θ, hθ, he⟩ := IsLevyFormula.ordinaryForcing_definition_uniform.{u}
    hχ (by omega)
  refine ⟨levyUniqueNameGraphFormula (unaryNameOutputFormula θ),
    levyUniqueNameGraphFormula_sigma (hθ.subst _), ?_⟩
  intro V _ _ _ N P R one τ hR ht hτ
  apply eval_levyUniqueNameGraphFormula _ N P R τ (standardTuple ![τ])
    (fun b ν ↦ forcingFormula P R φ (assignmentPrepend (1 : V) b ν)) (by definability)
  intro ν hν p
  have hnames : ∀ i : Fin 2, IsForcingName P ((![ν, τ] : Fin 2 → V) i) := by
    intro i
    exact Fin.cases hν (fun j ↦ Fin.cases hτ (fun e ↦ Fin.elim0 e) j) i
  have hb : (unaryNameOutputFormula θ).Evalb ![P, R, τ, ν, p] ↔
      θ.Evalb ![P, R, p, ν, τ] := by
    simp [unaryNameOutputFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [hb, he V P R hR ![ν, τ] hnames p]
  let v : Fin 2 → ForcingName P := fun i ↦ ⟨![ν, τ] i, hnames i⟩
  constructor
  · intro h
    have hp := classForcingFormula_subset P R (IsForcingName P) (by definability)
      χ (standardTuple ![ν, τ]) p h
    exact forcingFormula_entailment χ φ
      (fun W _ _ _ b ↦ (hv W b).mp) hR ht hp v h
  · intro h
    have hp := classForcingFormula_subset P R (IsForcingName P) (by definability)
      φ (standardTuple ![ν, τ]) p h
    exact forcingFormula_entailment φ χ
      (fun W _ _ _ b ↦ (hv W b).mpr) hR ht hp v h

end ZFVP

