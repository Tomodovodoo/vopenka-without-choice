import ZFVP.SetTheory.LevyGraphAssembly
import ZFVP.SetTheory.BoundedValue
import ZFVP.SetTheory.ForcingLimitColumns

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedThreadCoordinateFormula : SetTheorySemisentence 3 := graphAssemblyFormula boundedValueFormula

theorem boundedThreadCoordinateFormula_bounded : IsBoundedSetFormula boundedThreadCoordinateFormula :=
  graphAssemblyFormula_bounded boundedValueFormula_bounded

def boundedThreadCoordinateRow : SetTheorySemisentence 3 :=
  “y i C. !boundedThreadCoordinateFormula y C i”

theorem boundedThreadCoordinateRow_bounded : IsBoundedSetFormula boundedThreadCoordinateRow :=
  boundedThreadCoordinateFormula_bounded.subst _

def boundedLimitProjectionColumnFormula : SetTheorySemisentence 3 :=
  graphAssemblyFormula boundedThreadCoordinateRow

theorem boundedLimitProjectionColumnFormula_bounded : IsBoundedSetFormula boundedLimitProjectionColumnFormula :=
  graphAssemblyFormula_bounded boundedThreadCoordinateRow_bounded

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedThreadCoordinateFormula (G C i : V) :
    boundedThreadCoordinateFormula.Evalb ![G, C, i] ↔ G = forcingThreadCoordinate C i := by
  exact eval_graphAssemblyFormula boundedValueFormula G C ![i] (fun f ↦ f ‘ i)
    (by definability) (fun f _ y ↦ by simp)

instance boundedThreadCoordinateFormula_defined :
    ℒₛₑₜ-function₂[V] forcingThreadCoordinate via boundedThreadCoordinateFormula :=
  ⟨fun v ↦ by
    change boundedThreadCoordinateFormula.Evalb v ↔ v 0 = forcingThreadCoordinate (v 1) (v 2)
    have hv : v = ![v 0, v 1, v 2] := by
      funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i) i
    exact (Iff.of_eq (congrArg (fun w ↦ boundedThreadCoordinateFormula.Evalb w) hv)).trans
      (eval_boundedThreadCoordinateFormula (v 0) (v 1) (v 2))⟩

theorem eval_boundedLimitProjectionColumnFormula (G θ C : V) :
    boundedLimitProjectionColumnFormula.Evalb ![G, θ, C] ↔ G = forcingLimitProjectionColumn θ C := by
  apply eval_graphAssemblyFormula boundedThreadCoordinateRow G θ ![C]
    (forcingThreadCoordinate C) (forcingThreadCoordinate_parameter_definable C)
  intro i _ y
  simp [boundedThreadCoordinateRow]

instance boundedLimitProjectionColumnFormula_defined :
    ℒₛₑₜ-function₂[V] forcingLimitProjectionColumn via boundedLimitProjectionColumnFormula :=
  ⟨fun v ↦ by
    change boundedLimitProjectionColumnFormula.Evalb v ↔ v 0 = forcingLimitProjectionColumn (v 1) (v 2)
    have hv : v = ![v 0, v 1, v 2] := by
      funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i) i
    exact (Iff.of_eq (congrArg (fun w ↦ boundedLimitProjectionColumnFormula.Evalb w) hv)).trans
      (eval_boundedLimitProjectionColumnFormula (v 0) (v 1) (v 2))⟩

end ZFVP
