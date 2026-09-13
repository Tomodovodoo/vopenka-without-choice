import ZFVP.SetTheory.LevyGraphAssembly
import ZFVP.SetTheory.BoundedValue
import ZFVP.SetTheory.ForcingSystemExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedFamilyNextValueFormula : SetTheorySemisentence 5 :=
  “y i θ P Q. (i = θ ∧ y = Q) ∨ (i ≠ θ ∧ !boundedValueFormula y P i)”

theorem boundedFamilyNextValueFormula_bounded : IsBoundedSetFormula boundedFamilyNextValueFormula :=
  .or (.and (.rel _ _) (.rel _ _)) (.and (.nrel _ _) (boundedValueFormula_bounded.subst _))

def sigmaOneFamilyNextFormula : SetTheorySemisentence 4 :=
  “G θ P Q. ∃ A, !boundedSuccFormula A θ ∧ !(graphAssemblyFormula boundedFamilyNextValueFormula) G A θ P Q”

def piOneFamilyNextFormula : SetTheorySemisentence 4 :=
  “G θ P Q. ∀ A, !boundedSuccFormula A θ → !(graphAssemblyFormula boundedFamilyNextValueFormula) G A θ P Q”

theorem sigmaOneFamilyNextFormula_sigmaOne : IsSigmaFormula 1 sigmaOneFamilyNextFormula :=
  .exs (.bounded (.and (boundedSuccFormula_bounded.subst _)
    ((graphAssemblyFormula_bounded boundedFamilyNextValueFormula_bounded).subst _)))

theorem piOneFamilyNextFormula_piOne : IsPiFormula 1 piOneFamilyNextFormula :=
  .all (.bounded (.or (boundedSuccFormula_bounded.subst _).neg
    ((graphAssemblyFormula_bounded boundedFamilyNextValueFormula_bounded).subst _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedFamilyNextValueFormula (y i θ P Q : V) :
    boundedFamilyNextValueFormula.Evalb ![y, i, θ, P, Q] ↔ y = forcingFamilyNextValue θ P Q i := by
  classical
  by_cases hi : i = θ <;> simp [boundedFamilyNextValueFormula, forcingFamilyNextValue, hi]

theorem eval_familyNextGraphAssembly (G θ P Q : V) :
    (graphAssemblyFormula boundedFamilyNextValueFormula).Evalb ![G, succ θ, θ, P, Q] ↔
      G = forcingFamilyNext θ P Q := by
  exact eval_graphAssemblyFormula boundedFamilyNextValueFormula G (succ θ) ![θ, P, Q]
    (forcingFamilyNextValue θ P Q) (by
      exact Language.DefinableFunction₄.comp (F := forcingFamilyNextValue)
        (by definability) (by definability) (by definability) (by definability))
    (fun i _ y ↦ eval_boundedFamilyNextValueFormula y i θ P Q)

theorem eval_sigmaOneFamilyNextFormula (G θ P Q : V) :
    sigmaOneFamilyNextFormula.Evalb ![G, θ, P, Q] ↔ G = forcingFamilyNext θ P Q := by
  have he : sigmaOneFamilyNextFormula.Evalb ![G, θ, P, Q] ↔
      (graphAssemblyFormula boundedFamilyNextValueFormula).Evalb ![G, succ θ, θ, P, Q] := by
    simp [sigmaOneFamilyNextFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  exact he.trans (eval_familyNextGraphAssembly G θ P Q)

theorem eval_piOneFamilyNextFormula (G θ P Q : V) :
    piOneFamilyNextFormula.Evalb ![G, θ, P, Q] ↔ G = forcingFamilyNext θ P Q := by
  have he : piOneFamilyNextFormula.Evalb ![G, θ, P, Q] ↔
      (graphAssemblyFormula boundedFamilyNextValueFormula).Evalb ![G, succ θ, θ, P, Q] := by
    simp [piOneFamilyNextFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  exact he.trans (eval_familyNextGraphAssembly G θ P Q)

instance sigmaOneFamilyNextFormula_defined : ℒₛₑₜ-function₃[V] forcingFamilyNext via sigmaOneFamilyNextFormula :=
  ⟨fun v ↦ by
    change sigmaOneFamilyNextFormula.Evalb v ↔ v 0 = forcingFamilyNext (v 1) (v 2) (v 3)
    have hv : v = ![v 0, v 1, v 2, v 3] := by
      funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i) i) i
    exact (Iff.of_eq (congrArg (fun w ↦ sigmaOneFamilyNextFormula.Evalb w) hv)).trans
      (eval_sigmaOneFamilyNextFormula (v 0) (v 1) (v 2) (v 3))⟩

instance piOneFamilyNextFormula_defined : ℒₛₑₜ-function₃[V] forcingFamilyNext via piOneFamilyNextFormula :=
  ⟨fun v ↦ by
    change piOneFamilyNextFormula.Evalb v ↔ v 0 = forcingFamilyNext (v 1) (v 2) (v 3)
    have hv : v = ![v 0, v 1, v 2, v 3] := by
      funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i) i) i
    exact (Iff.of_eq (congrArg (fun w ↦ piOneFamilyNextFormula.Evalb w) hv)).trans
      (eval_piOneFamilyNextFormula (v 0) (v 1) (v 2) (v 3))⟩

end ZFVP
