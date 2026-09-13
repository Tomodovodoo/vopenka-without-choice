import ZFVP.SetTheory.DeltaOneFamilyNext
import ZFVP.SetTheory.BoundedProduct

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedMatrixNextValueFormula : SetTheorySemisentence 6 :=
  “y a θ M C d. ∃ u ∈ a, ∃ i ∈ u, ∃ v ∈ a, ∃ j ∈ v,
    !boundedKpairFormula a i j ∧ ((j = θ ∧ !boundedFamilyNextValueFormula y i θ C d) ∨
      (j ≠ θ ∧ !boundedValueFormula y M a))”

theorem boundedMatrixNextValueFormula_bounded : IsBoundedSetFormula boundedMatrixNextValueFormula :=
  .exs (.bvar 1) (.exs (.bvar 0) (.exs (.bvar 3) (.exs (.bvar 0)
    (.and (boundedKpairFormula_bounded.subst _) (.or
      (.and (.rel _ _) (boundedFamilyNextValueFormula_bounded.subst _))
      (.and (.nrel _ _) (boundedValueFormula_bounded.subst _)))))))

def sigmaOneMatrixNextFormula : SetTheorySemisentence 5 :=
  “G θ M C d. ∃ B, ∃ A, !boundedSuccFormula B θ ∧ !boundedProductFormula A B B ∧
    !(graphAssemblyFormula boundedMatrixNextValueFormula) G A θ M C d”

def piOneMatrixNextFormula : SetTheorySemisentence 5 :=
  “G θ M C d. ∀ B, ∀ A, !boundedSuccFormula B θ → !boundedProductFormula A B B →
    !(graphAssemblyFormula boundedMatrixNextValueFormula) G A θ M C d”

theorem sigmaOneMatrixNextFormula_sigmaOne : IsSigmaFormula 1 sigmaOneMatrixNextFormula :=
  .exs (.exs (.bounded (.and (boundedSuccFormula_bounded.subst _)
    (.and (boundedProductFormula_bounded.subst _)
      ((graphAssemblyFormula_bounded boundedMatrixNextValueFormula_bounded).subst _)))))

theorem piOneMatrixNextFormula_piOne : IsPiFormula 1 piOneMatrixNextFormula :=
  .all (.all (.bounded (.or (boundedSuccFormula_bounded.subst _).neg
    (.or (boundedProductFormula_bounded.subst _).neg
      ((graphAssemblyFormula_bounded boundedMatrixNextValueFormula_bounded).subst _)))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedMatrixNextValueFormula_pair (y i j θ M C d : V) :
    boundedMatrixNextValueFormula.Evalb ![y, ⟨i, j⟩ₖ, θ, M, C, d] ↔
      y = forcingMatrixNextValue θ M C d ⟨i, j⟩ₖ := by
  classical
  have he : boundedMatrixNextValueFormula.Evalb ![y, ⟨i, j⟩ₖ, θ, M, C, d] ↔
      ∃ u ∈ ⟨i, j⟩ₖ, ∃ a ∈ u, ∃ v ∈ ⟨i, j⟩ₖ, ∃ b ∈ v,
        ⟨i, j⟩ₖ = ⟨a, b⟩ₖ ∧ ((b = θ ∧ y = forcingFamilyNextValue θ C d a) ∨
          (b ≠ θ ∧ y = M ‘ ⟨i, j⟩ₖ)) := by
    have hf := eval_boundedFamilyNextValueFormula y i θ C d
    simp only [Semiformula.Evalb] at hf
    simp [boundedMatrixNextValueFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, hf]
  rw [he]
  constructor
  · rintro ⟨u, _, a, _, v, _, b, _, hab, h⟩
    obtain ⟨rfl, rfl⟩ := kpair_inj hab
    by_cases hj : j = θ <;> simpa [forcingMatrixNextValue, hj] using h
  · intro h
    refine ⟨doubleton i j, by simp [kpair, pair_eq_doubleton], i, by simp,
      doubleton i j, by simp [kpair, pair_eq_doubleton], j, by simp, rfl, ?_⟩
    by_cases hj : j = θ <;> simpa [forcingMatrixNextValue, hj] using h

theorem eval_matrixNextGraphAssembly (G θ M C d : V) :
    (graphAssemblyFormula boundedMatrixNextValueFormula).Evalb
      ![G, succ θ ×ˢ succ θ, θ, M, C, d] ↔ G = forcingMatrixNext θ M C d := by
  apply eval_graphAssemblyFormula boundedMatrixNextValueFormula G (succ θ ×ˢ succ θ)
    ![θ, M, C, d] (forcingMatrixNextValue θ M C d)
    (forcingMatrixNextValue_parameter_definable θ M C d)
  intro a ha y
  obtain ⟨i, _, j, _, rfl⟩ := mem_prod_iff.mp ha
  exact eval_boundedMatrixNextValueFormula_pair y i j θ M C d

theorem eval_sigmaOneMatrixNextFormula (G θ M C d : V) :
    sigmaOneMatrixNextFormula.Evalb ![G, θ, M, C, d] ↔ G = forcingMatrixNext θ M C d := by
  have he : sigmaOneMatrixNextFormula.Evalb ![G, θ, M, C, d] ↔
      (graphAssemblyFormula boundedMatrixNextValueFormula).Evalb
        ![G, succ θ ×ˢ succ θ, θ, M, C, d] := by
    simp [sigmaOneMatrixNextFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  exact he.trans (eval_matrixNextGraphAssembly G θ M C d)

theorem eval_piOneMatrixNextFormula (G θ M C d : V) :
    piOneMatrixNextFormula.Evalb ![G, θ, M, C, d] ↔ G = forcingMatrixNext θ M C d := by
  have he : piOneMatrixNextFormula.Evalb ![G, θ, M, C, d] ↔
      (graphAssemblyFormula boundedMatrixNextValueFormula).Evalb
        ![G, succ θ ×ˢ succ θ, θ, M, C, d] := by
    simp [piOneMatrixNextFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  exact he.trans (eval_matrixNextGraphAssembly G θ M C d)

instance sigmaOneMatrixNextFormula_defined : ℒₛₑₜ-function₄[V] forcingMatrixNext via sigmaOneMatrixNextFormula :=
  ⟨fun v ↦ by
    change sigmaOneMatrixNextFormula.Evalb v ↔ v 0 = forcingMatrixNext (v 1) (v 2) (v 3) (v 4)
    have hv : v = ![v 0, v 1, v 2, v 3, v 4] := by
      funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i) i) i) i
    exact (Iff.of_eq (congrArg (fun w ↦ sigmaOneMatrixNextFormula.Evalb w) hv)).trans
      (eval_sigmaOneMatrixNextFormula (v 0) (v 1) (v 2) (v 3) (v 4))⟩

instance piOneMatrixNextFormula_defined : ℒₛₑₜ-function₄[V] forcingMatrixNext via piOneMatrixNextFormula :=
  ⟨fun v ↦ by
    change piOneMatrixNextFormula.Evalb v ↔ v 0 = forcingMatrixNext (v 1) (v 2) (v 3) (v 4)
    have hv : v = ![v 0, v 1, v 2, v 3, v 4] := by
      funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i) i) i) i
    exact (Iff.of_eq (congrArg (fun w ↦ piOneMatrixNextFormula.Evalb w) hv)).trans
      (eval_piOneMatrixNextFormula (v 0) (v 1) (v 2) (v 3) (v 4))⟩

end ZFVP
