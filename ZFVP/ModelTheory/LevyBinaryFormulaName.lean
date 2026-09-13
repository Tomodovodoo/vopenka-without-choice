import ZFVP.ModelTheory.LevyUnaryFormulaName
import ZFVP.ModelTheory.ForcingEntailment
import ZFVP.Syntax.SigmaOneBinaryTuple

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def binaryNameOutputFormula (θ : SetTheorySemisentence 6) : SetTheorySemisentence 5 :=
  “P R a ν p. ∃ x, ∃ y, !sigmaOneBinaryTupleFormula a x y ∧ !θ P R p ν x y”

def binaryNameGraphFormula (θ : SetTheorySemisentence 6) : SetTheorySemisentence 5 :=
  “N P R x y. ∃ a, !sigmaOneBinaryTupleFormula a x y ∧
    !(levyUniqueNameGraphFormula (binaryNameOutputFormula θ)) N P R a”

theorem binaryNameOutputFormula_sigma {k : ℕ} {θ : SetTheorySemisentence 6}
    (hθ : IsSigmaFormula (k + 1) θ) : IsSigmaFormula (k + 1) (binaryNameOutputFormula θ) :=
  .exs (.exs (.and ((sigmaOneBinaryTupleFormula_sigmaOne.mono (by omega)).subst _) (hθ.subst _)))

theorem binaryNameGraphFormula_sigma {k : ℕ} {θ : SetTheorySemisentence 6}
    (hθ : IsSigmaFormula (k + 1) θ) : IsSigmaFormula (k + 2) (binaryNameGraphFormula θ) :=
  .exs (.and ((sigmaOneBinaryTupleFormula_sigmaOne.mono (by omega)).subst _)
    ((levyUniqueNameGraphFormula_sigma (binaryNameOutputFormula_sigma hθ)).subst _))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_binaryNameOutputFormula (θ : SetTheorySemisentence 6) (P R x y ν p : V) :
    (binaryNameOutputFormula θ).Evalb ![P, R, standardTuple ![x, y], ν, p] ↔
      θ.Evalb ![P, R, p, ν, x, y] := by
  have he : (binaryNameOutputFormula θ).Evalb ![P, R, standardTuple ![x, y], ν, p] ↔
      ∃ z w : V, standardTuple ![x, y] = standardTuple ![z, w] ∧ θ.Evalb ![P, R, p, ν, z, w] := by
    simp [binaryNameOutputFormula, eval_sigmaOneBinaryTupleFormula, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  rw [he]
  constructor
  · rintro ⟨z, w, ht, h⟩
    have hv := standardTuple_injective ht
    have hx : x = z := congrFun hv 0
    have hy : y = w := congrFun hv 1
    simpa only [← hx, ← hy] using h
  · intro h
    exact ⟨x, y, rfl, h⟩

theorem binaryFormulaName_sigma_uniform_of_equiv {k : ℕ} (φ χ : SetTheorySemisentence 3)
    (hχ : IsSigmaFormula (k + 1) χ)
    (hv : ∀ (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
      ∀ v : Fin 3 → W, χ.Evalb v ↔ φ.Evalb v) :
    ∃ Λ : SetTheorySemisentence 5, IsSigmaFormula (k + 2) Λ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ N P R one x y : V, IsForcingPreorder P R → IsForcingTop P R one →
          IsForcingName P x → IsForcingName P y →
          (Λ.Evalb ![N, P, R, x, y] ↔ N = formulaUniqueName P R φ (standardTuple ![x, y])) := by
  obtain ⟨θ, hθ, he⟩ := IsLevyFormula.ordinaryForcing_definition_uniform.{u} hχ (by omega)
  refine ⟨binaryNameGraphFormula θ, binaryNameGraphFormula_sigma hθ, ?_⟩
  intro V _ _ _ N P R one x y hR ht hx hy
  have hb : (binaryNameGraphFormula θ).Evalb ![N, P, R, x, y] ↔
      (levyUniqueNameGraphFormula (binaryNameOutputFormula θ)).Evalb ![N, P, R, standardTuple ![x, y]] := by
    simp [binaryNameGraphFormula, eval_sigmaOneBinaryTupleFormula, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  rw [hb]
  apply eval_levyUniqueNameGraphFormula _ N P R (standardTuple ![x, y]) (standardTuple ![x, y])
    (fun b ν ↦ forcingFormula P R φ (assignmentPrepend (2 : V) b ν)) (by definability)
  intro ν hν p
  rw [eval_binaryNameOutputFormula]
  have hnames : ∀ i : Fin 3, IsForcingName P ((![ν, x, y] : Fin 3 → V) i) := by
    intro i
    exact Fin.cases hν (fun j ↦ Fin.cases hx (fun t ↦ Fin.cases hy (fun e ↦ Fin.elim0 e) t) j) i
  rw [he V P R hR ![ν, x, y] hnames p]
  let v : Fin 3 → ForcingName P := fun i ↦ ⟨![ν, x, y] i, hnames i⟩
  constructor
  · intro h
    have hp := classForcingFormula_subset P R (IsForcingName P) (by definability) χ (standardTuple ![ν, x, y]) p h
    exact forcingFormula_entailment χ φ (fun W _ _ _ b ↦ (hv W b).mp) hR ht hp v h
  · intro h
    have hp := classForcingFormula_subset P R (IsForcingName P) (by definability) φ (standardTuple ![ν, x, y]) p h
    exact forcingFormula_entailment φ χ (fun W _ _ _ b ↦ (hv W b).mpr) hR ht hp v h

end ZFVP

