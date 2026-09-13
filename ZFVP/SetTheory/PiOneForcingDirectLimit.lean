import ZFVP.SetTheory.PiOneForcingInverseLimit
import ZFVP.SetTheory.ForcingDirectLimit

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneSectionCoordinateFormula : SetTheorySemisentence 4 :=
  “E f k j. ∃ c, ∃ g, ∃ x, ∃ y, !boundedKpairFormula c k j ∧ !boundedValueFormula g E c ∧
    !boundedValueFormula x f k ∧ !boundedValueFormula y f j ∧ !boundedValueFormula y g x”

def piOneSectionCoordinateFormula : SetTheorySemisentence 4 :=
  “E f k j. ∀ c, ∀ g, ∀ x, ∀ y, !boundedKpairFormula c k j → !boundedValueFormula g E c →
    !boundedValueFormula x f k → !boundedValueFormula y f j → !boundedValueFormula y g x”

theorem sigmaOneSectionCoordinateFormula_sigmaOne : IsSigmaFormula 1 sigmaOneSectionCoordinateFormula :=
  .exs (.exs (.exs (.exs (.bounded (.and (boundedKpairFormula_bounded.subst _)
    (.and (boundedValueFormula_bounded.subst _) (.and (boundedValueFormula_bounded.subst _)
      (.and (boundedValueFormula_bounded.subst _) (boundedValueFormula_bounded.subst _)))))))))

theorem piOneSectionCoordinateFormula_piOne : IsPiFormula 1 piOneSectionCoordinateFormula :=
  .all (.all (.all (.all (.bounded (.or (boundedKpairFormula_bounded.subst _).neg
    (.or (boundedValueFormula_bounded.subst _).neg (.or (boundedValueFormula_bounded.subst _).neg
      (.or (boundedValueFormula_bounded.subst _).neg (boundedValueFormula_bounded.subst _)))))))))

def threadSupportExistsFormula (coord : SetTheorySemisentence 4) : SetTheorySemisentence 3 :=
  “θ E f. ∃ k ∈ θ, ∀ j ∈ θ, !isSubsetOf k j → !coord E f k j”

theorem threadSupportExistsFormula_levy {s : LevyPolarity} {k : ℕ} {coord : SetTheorySemisentence 4}
    (hc : IsLevyFormula s k coord) : IsLevyFormula s k (threadSupportExistsFormula coord) :=
  .boundedExs (.bvar 0) (.boundedAll (.bvar 1) (.or (.bounded (isSubsetOf_bounded.subst _).neg) (hc.subst _)))

def sigmaOneDirectThreadConditionFormula : SetTheorySemisentence 6 :=
  “f θ P π E U. !sigmaOneInverseThreadConditionFormula f θ P π U ∧
    !(threadSupportExistsFormula sigmaOneSectionCoordinateFormula) θ E f”

def piOneDirectThreadConditionFormula : SetTheorySemisentence 6 :=
  “f θ P π E U. !piOneInverseThreadConditionFormula f θ P π U ∧
    !(threadSupportExistsFormula piOneSectionCoordinateFormula) θ E f”

theorem sigmaOneDirectThreadConditionFormula_sigmaOne : IsSigmaFormula 1 sigmaOneDirectThreadConditionFormula :=
  .and (sigmaOneInverseThreadConditionFormula_sigmaOne.subst _)
    ((threadSupportExistsFormula_levy sigmaOneSectionCoordinateFormula_sigmaOne).subst _)

theorem piOneDirectThreadConditionFormula_piOne : IsPiFormula 1 piOneDirectThreadConditionFormula :=
  .and (piOneInverseThreadConditionFormula_piOne.subst _)
    ((threadSupportExistsFormula_levy piOneSectionCoordinateFormula_piOne).subst _)

def piOneDirectLimitGraphFormula : SetTheorySemisentence 6 :=
  “C θ P π E U. ∀ f, (f ∈ C → !piOneDirectThreadConditionFormula f θ P π E U) ∧
    (!sigmaOneDirectThreadConditionFormula f θ P π E U → f ∈ C)”

theorem piOneDirectLimitGraphFormula_piOne : IsPiFormula 1 piOneDirectLimitGraphFormula :=
  .all (.and (.or (.bounded (.nrel _ _)) (piOneDirectThreadConditionFormula_piOne.subst _))
    (.or (sigmaOneDirectThreadConditionFormula_sigmaOne.subst _).neg (.bounded (.rel _ _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaOneSectionCoordinateFormula (E f k j : V) :
    sigmaOneSectionCoordinateFormula.Evalb ![E, f, k, j] ↔ f ‘ j = (E ‘ ⟨k, j⟩ₖ) ‘ (f ‘ k) := by
  simp [sigmaOneSectionCoordinateFormula]

theorem eval_piOneSectionCoordinateFormula (E f k j : V) :
    piOneSectionCoordinateFormula.Evalb ![E, f, k, j] ↔ f ‘ j = (E ‘ ⟨k, j⟩ₖ) ‘ (f ‘ k) := by
  simp [piOneSectionCoordinateFormula]
  constructor
  · intro h
    exact h _ _ _ _ rfl rfl rfl rfl
  · rintro h c g x y rfl rfl rfl rfl
    exact h

theorem eval_sigmaOneThreadSupportExistsFormula (θ E f : V) :
    (threadSupportExistsFormula sigmaOneSectionCoordinateFormula).Evalb ![θ, E, f] ↔
      ∃ k, IsThreadSupport θ E f k := by
  simp [threadSupportExistsFormula, eval_sigmaOneSectionCoordinateFormula, IsThreadSupport,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]

theorem eval_piOneThreadSupportExistsFormula (θ E f : V) :
    (threadSupportExistsFormula piOneSectionCoordinateFormula).Evalb ![θ, E, f] ↔
      ∃ k, IsThreadSupport θ E f k := by
  simp [threadSupportExistsFormula, eval_piOneSectionCoordinateFormula, IsThreadSupport,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]

theorem eval_sigmaOneDirectThreadConditionFormula (f θ P π E U : V) :
    sigmaOneDirectThreadConditionFormula.Evalb ![f, θ, P, π, E, U] ↔ f ∈ forcingDirectLimit θ P π E U := by
  simp [sigmaOneDirectThreadConditionFormula, eval_sigmaOneInverseThreadConditionFormula,
    eval_sigmaOneThreadSupportExistsFormula, mem_forcingDirectLimit_iff,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]

theorem eval_piOneDirectThreadConditionFormula (f θ P π E U : V) :
    piOneDirectThreadConditionFormula.Evalb ![f, θ, P, π, E, U] ↔ f ∈ forcingDirectLimit θ P π E U := by
  simp [piOneDirectThreadConditionFormula, eval_piOneInverseThreadConditionFormula,
    eval_piOneThreadSupportExistsFormula, mem_forcingDirectLimit_iff,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]

theorem eval_piOneDirectLimitGraphFormula (C θ P π E U : V) :
    piOneDirectLimitGraphFormula.Evalb ![C, θ, P, π, E, U] ↔ C = forcingDirectLimit θ P π E U := by
  rw [mem_ext_iff]
  simp [piOneDirectLimitGraphFormula, eval_sigmaOneDirectThreadConditionFormula,
    eval_piOneDirectThreadConditionFormula, iff_iff_implies_and_implies,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]

instance piOneDirectLimitGraphFormula_defined : ℒₛₑₜ-function₅[V] forcingDirectLimit via piOneDirectLimitGraphFormula :=
  ⟨fun v ↦ by
    change piOneDirectLimitGraphFormula.Evalb v ↔ v 0 = forcingDirectLimit (v 1) (v 2) (v 3) (v 4) (v 5)
    have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5] := by
      funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i) i) i) i) i
    exact (Iff.of_eq (congrArg (fun w ↦ piOneDirectLimitGraphFormula.Evalb w) hv)).trans
      (eval_piOneDirectLimitGraphFormula (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))⟩

end ZFVP
