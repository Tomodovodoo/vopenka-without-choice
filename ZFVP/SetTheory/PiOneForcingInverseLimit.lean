import ZFVP.SetTheory.ForcingInverseLimit
import ZFVP.SetTheory.BoundedValue

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneThreadCoordinateFormula : SetTheorySemisentence 3 :=
  “P f i. ∃ x, ∃ y, !boundedValueFormula x f i ∧ !boundedValueFormula y P i ∧ x ∈ y”

def piOneThreadCoordinateFormula : SetTheorySemisentence 3 :=
  “P f i. ∀ x, ∀ y, !boundedValueFormula x f i → !boundedValueFormula y P i → x ∈ y”

def sigmaOneThreadCoherenceFormula : SetTheorySemisentence 4 :=
  “π f i j. ∃ c, ∃ g, ∃ x, ∃ y, !boundedKpairFormula c i j ∧ !boundedValueFormula g π c ∧
    !boundedValueFormula x f j ∧ !boundedValueFormula y f i ∧ !boundedValueFormula y g x”

def piOneThreadCoherenceFormula : SetTheorySemisentence 4 :=
  “π f i j. ∀ c, ∀ g, ∀ x, ∀ y, !boundedKpairFormula c i j → !boundedValueFormula g π c →
    !boundedValueFormula x f j → !boundedValueFormula y f i → !boundedValueFormula y g x”

theorem sigmaOneThreadCoordinateFormula_sigmaOne : IsSigmaFormula 1 sigmaOneThreadCoordinateFormula :=
  .exs (.exs (.bounded (.and (boundedValueFormula_bounded.subst _)
    (.and (boundedValueFormula_bounded.subst _) (.rel _ _)))))

theorem piOneThreadCoordinateFormula_piOne : IsPiFormula 1 piOneThreadCoordinateFormula :=
  .all (.all (.bounded (.or (boundedValueFormula_bounded.subst _).neg
    (.or (boundedValueFormula_bounded.subst _).neg (.rel _ _)))))

theorem sigmaOneThreadCoherenceFormula_sigmaOne : IsSigmaFormula 1 sigmaOneThreadCoherenceFormula :=
  .exs (.exs (.exs (.exs (.bounded (.and (boundedKpairFormula_bounded.subst _)
    (.and (boundedValueFormula_bounded.subst _) (.and (boundedValueFormula_bounded.subst _)
      (.and (boundedValueFormula_bounded.subst _) (boundedValueFormula_bounded.subst _)))))))))

theorem piOneThreadCoherenceFormula_piOne : IsPiFormula 1 piOneThreadCoherenceFormula :=
  .all (.all (.all (.all (.bounded (.or (boundedKpairFormula_bounded.subst _).neg
    (.or (boundedValueFormula_bounded.subst _).neg (.or (boundedValueFormula_bounded.subst _).neg
      (.or (boundedValueFormula_bounded.subst _).neg (boundedValueFormula_bounded.subst _)))))))))

def inverseThreadConditionFormula (coord : SetTheorySemisentence 3) (coh : SetTheorySemisentence 4) :
    SetTheorySemisentence 5 :=
  “f θ P π U. !boundedFunctionFormula f θ U ∧ (∀ i ∈ θ, !coord P f i) ∧
    ∀ j ∈ θ, ∀ i ∈ j, i ∈ θ → !coh π f i j”

theorem inverseThreadConditionFormula_levy {s : LevyPolarity} {k : ℕ}
    {coord : SetTheorySemisentence 3} {coh : SetTheorySemisentence 4}
    (hc : IsLevyFormula s k coord) (hh : IsLevyFormula s k coh) :
    IsLevyFormula s k (inverseThreadConditionFormula coord coh) :=
  .and (.bounded (boundedFunctionFormula_bounded.subst _))
    (.and (.boundedAll (.bvar 1) (hc.subst _))
      (.boundedAll (.bvar 1) (.boundedAll (.bvar 0) (.or (.bounded (.nrel _ _)) (hh.subst _)))))

def sigmaOneInverseThreadConditionFormula : SetTheorySemisentence 5 :=
  inverseThreadConditionFormula sigmaOneThreadCoordinateFormula sigmaOneThreadCoherenceFormula

def piOneInverseThreadConditionFormula : SetTheorySemisentence 5 :=
  inverseThreadConditionFormula piOneThreadCoordinateFormula piOneThreadCoherenceFormula

theorem sigmaOneInverseThreadConditionFormula_sigmaOne : IsSigmaFormula 1 sigmaOneInverseThreadConditionFormula :=
  inverseThreadConditionFormula_levy sigmaOneThreadCoordinateFormula_sigmaOne sigmaOneThreadCoherenceFormula_sigmaOne

theorem piOneInverseThreadConditionFormula_piOne : IsPiFormula 1 piOneInverseThreadConditionFormula :=
  inverseThreadConditionFormula_levy piOneThreadCoordinateFormula_piOne piOneThreadCoherenceFormula_piOne

def piOneInverseLimitGraphFormula : SetTheorySemisentence 5 :=
  “C θ P π U. ∀ f, (f ∈ C → !piOneInverseThreadConditionFormula f θ P π U) ∧
    (!sigmaOneInverseThreadConditionFormula f θ P π U → f ∈ C)”

theorem piOneInverseLimitGraphFormula_piOne : IsPiFormula 1 piOneInverseLimitGraphFormula :=
  .all (.and (.or (.bounded (.nrel _ _)) (piOneInverseThreadConditionFormula_piOne.subst _))
    (.or (sigmaOneInverseThreadConditionFormula_sigmaOne.subst _).neg (.bounded (.rel _ _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaOneThreadCoordinateFormula (P f i : V) :
    sigmaOneThreadCoordinateFormula.Evalb ![P, f, i] ↔ f ‘ i ∈ P ‘ i := by
  simp [sigmaOneThreadCoordinateFormula]

theorem eval_piOneThreadCoordinateFormula (P f i : V) :
    piOneThreadCoordinateFormula.Evalb ![P, f, i] ↔ f ‘ i ∈ P ‘ i := by
  simp [piOneThreadCoordinateFormula]

theorem eval_sigmaOneThreadCoherenceFormula (π f i j : V) :
    sigmaOneThreadCoherenceFormula.Evalb ![π, f, i, j] ↔ (π ‘ ⟨i, j⟩ₖ) ‘ (f ‘ j) = f ‘ i := by
  simp [sigmaOneThreadCoherenceFormula, eq_comm]

theorem eval_piOneThreadCoherenceFormula (π f i j : V) :
    piOneThreadCoherenceFormula.Evalb ![π, f, i, j] ↔ (π ‘ ⟨i, j⟩ₖ) ‘ (f ‘ j) = f ‘ i := by
  simp [piOneThreadCoherenceFormula, eq_comm]
  constructor
  · intro h
    exact h _ _ _ _ rfl rfl rfl rfl
  · rintro h c g x y rfl rfl rfl rfl
    exact h

theorem eval_sigmaOneInverseThreadConditionFormula (f θ P π U : V) :
    sigmaOneInverseThreadConditionFormula.Evalb ![f, θ, P, π, U] ↔ f ∈ forcingInverseLimit θ P π U := by
  simp [sigmaOneInverseThreadConditionFormula, inverseThreadConditionFormula,
    eval_sigmaOneThreadCoordinateFormula, eval_sigmaOneThreadCoherenceFormula, mem_forcingInverseLimit_iff,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]

theorem eval_piOneInverseThreadConditionFormula (f θ P π U : V) :
    piOneInverseThreadConditionFormula.Evalb ![f, θ, P, π, U] ↔ f ∈ forcingInverseLimit θ P π U := by
  simp [piOneInverseThreadConditionFormula, inverseThreadConditionFormula,
    eval_piOneThreadCoordinateFormula, eval_piOneThreadCoherenceFormula, mem_forcingInverseLimit_iff,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]

theorem eval_piOneInverseLimitGraphFormula (C θ P π U : V) :
    piOneInverseLimitGraphFormula.Evalb ![C, θ, P, π, U] ↔ C = forcingInverseLimit θ P π U := by
  rw [mem_ext_iff]
  simp [piOneInverseLimitGraphFormula, eval_sigmaOneInverseThreadConditionFormula,
    eval_piOneInverseThreadConditionFormula, iff_iff_implies_and_implies,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]

instance piOneInverseLimitGraphFormula_defined : ℒₛₑₜ-function₄[V] forcingInverseLimit via piOneInverseLimitGraphFormula :=
  ⟨fun v ↦ by
    change piOneInverseLimitGraphFormula.Evalb v ↔ v 0 = forcingInverseLimit (v 1) (v 2) (v 3) (v 4)
    have hv : v = ![v 0, v 1, v 2, v 3, v 4] := by
      funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i) i) i) i
    exact (Iff.of_eq (congrArg (fun w ↦ piOneInverseLimitGraphFormula.Evalb w) hv)).trans
      (eval_piOneInverseLimitGraphFormula (v 0) (v 1) (v 2) (v 3) (v 4))⟩

end ZFVP
