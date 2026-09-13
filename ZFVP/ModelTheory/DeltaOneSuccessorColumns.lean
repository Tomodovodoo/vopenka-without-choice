import ZFVP.ModelTheory.DeltaOneSuccessorMaps

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def successorProjectionColumnRow : SetTheorySemisentence 5 :=
  “y i C π k. !sigmaOneSuccessorProjectionFormula y C π k i”

def successorSectionColumnRow : SetTheorySemisentence 6 :=
  “y i P E k t. !sigmaOneSuccessorSectionFormula y P E k t i”

def successorLiftColumnRow : SetTheorySemisentence 6 :=
  “y i C P L k. ∃ A, !boundedValueFormula A P i ∧
    ∃ j, !boundedKpairFormula j i k ∧ ∃ M, !boundedValueFormula M L j ∧
    !sigmaOneSuccessorLiftFormula y C A M”

def sigmaOneSuccessorProjectionColumnFormula : SetTheorySemisentence 5 := graphAssemblyFormula successorProjectionColumnRow
def sigmaOneSuccessorSectionColumnFormula : SetTheorySemisentence 6 := graphAssemblyFormula successorSectionColumnRow
def sigmaOneSuccessorLiftColumnFormula : SetTheorySemisentence 6 := graphAssemblyFormula successorLiftColumnRow

theorem sigmaOneSuccessorProjectionColumnFormula_sigmaOne : IsSigmaFormula 1 sigmaOneSuccessorProjectionColumnFormula :=
  graphAssemblyFormula_levy (sigmaOneSuccessorProjectionFormula_sigmaOne.subst _)

theorem sigmaOneSuccessorSectionColumnFormula_sigmaOne : IsSigmaFormula 1 sigmaOneSuccessorSectionColumnFormula :=
  graphAssemblyFormula_levy (sigmaOneSuccessorSectionFormula_sigmaOne.subst _)

theorem sigmaOneSuccessorLiftColumnFormula_sigmaOne : IsSigmaFormula 1 sigmaOneSuccessorLiftColumnFormula :=
  graphAssemblyFormula_levy (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedKpairFormula_bounded.subst _))
      (.exs (.and (.bounded (boundedValueFormula_bounded.subst _)) (sigmaOneSuccessorLiftFormula_sigmaOne.subst _)))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaOneSuccessorProjectionColumnFormula (G θ C π k : V) :
    sigmaOneSuccessorProjectionColumnFormula.Evalb ![G, θ, C, π, k] ↔ G = successorProjectionColumn θ C π k := by
  apply eval_graphAssemblyFormula successorProjectionColumnRow G θ ![C, π, k]
    (successorStageProjection C π k) (by definability)
  intro i _ y
  simp [successorProjectionColumnRow]

theorem eval_sigmaOneSuccessorSectionColumnFormula (G θ P E k t : V) :
    sigmaOneSuccessorSectionColumnFormula.Evalb ![G, θ, P, E, k, t] ↔ G = successorSectionColumn θ P E k t := by
  apply eval_graphAssemblyFormula successorSectionColumnRow G θ ![P, E, k, t]
    (successorStageSection P E k t) (by definability)
  intro i _ y
  simp [successorSectionColumnRow]

theorem eval_sigmaOneSuccessorLiftColumnFormula (G θ C P L k : V) :
    sigmaOneSuccessorLiftColumnFormula.Evalb ![G, θ, C, P, L, k] ↔ G = successorLiftColumn θ C P L k := by
  apply eval_graphAssemblyFormula successorLiftColumnRow G θ ![C, P, L, k]
    (fun i ↦ successorForcingLift C (P ‘ i) (L ‘ ⟨i, k⟩ₖ)) (by definability)
  intro i _ y
  simp [successorLiftColumnRow]

instance sigmaOneSuccessorProjectionColumnFormula_defined :
    ℒₛₑₜ-function₄[V] successorProjectionColumn via sigmaOneSuccessorProjectionColumnFormula :=
  ⟨fun v ↦ by
    have hv : v = ![v 0, v 1, v 2, v 3, v 4] := by funext i; fin_cases i <;> rfl
    change sigmaOneSuccessorProjectionColumnFormula.Evalb v ↔ _
    rw [hv]
    exact eval_sigmaOneSuccessorProjectionColumnFormula _ _ _ _ _⟩

instance sigmaOneSuccessorSectionColumnFormula_defined :
    ℒₛₑₜ-function₅[V] successorSectionColumn via sigmaOneSuccessorSectionColumnFormula :=
  ⟨fun v ↦ by
    have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5] := by funext i; fin_cases i <;> rfl
    change sigmaOneSuccessorSectionColumnFormula.Evalb v ↔ _
    rw [hv]
    exact eval_sigmaOneSuccessorSectionColumnFormula _ _ _ _ _ _⟩

instance sigmaOneSuccessorLiftColumnFormula_defined :
    ℒₛₑₜ-function₅[V] successorLiftColumn via sigmaOneSuccessorLiftColumnFormula :=
  ⟨fun v ↦ by
    have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5] := by funext i; fin_cases i <;> rfl
    change sigmaOneSuccessorLiftColumnFormula.Evalb v ↔ _
    rw [hv]
    exact eval_sigmaOneSuccessorLiftColumnFormula _ _ _ _ _ _⟩

def piOneSuccessorProjectionColumnFormula : SetTheorySemisentence 5 :=
  “G θ C π k. ∀ D, !sigmaOneSuccessorProjectionColumnFormula D θ C π k → G = D”
def piOneSuccessorSectionColumnFormula : SetTheorySemisentence 6 :=
  “G θ P E k t. ∀ D, !sigmaOneSuccessorSectionColumnFormula D θ P E k t → G = D”
def piOneSuccessorLiftColumnFormula : SetTheorySemisentence 6 :=
  “G θ C P L k. ∀ D, !sigmaOneSuccessorLiftColumnFormula D θ C P L k → G = D”

theorem piOneSuccessorProjectionColumnFormula_piOne : IsPiFormula 1 piOneSuccessorProjectionColumnFormula :=
  .all (.or (sigmaOneSuccessorProjectionColumnFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))
theorem piOneSuccessorSectionColumnFormula_piOne : IsPiFormula 1 piOneSuccessorSectionColumnFormula :=
  .all (.or (sigmaOneSuccessorSectionColumnFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))
theorem piOneSuccessorLiftColumnFormula_piOne : IsPiFormula 1 piOneSuccessorLiftColumnFormula :=
  .all (.or (sigmaOneSuccessorLiftColumnFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))

instance piOneSuccessorProjectionColumnFormula_defined :
    ℒₛₑₜ-function₄[V] successorProjectionColumn via piOneSuccessorProjectionColumnFormula :=
  ⟨fun v ↦ by simp [piOneSuccessorProjectionColumnFormula]⟩
instance piOneSuccessorSectionColumnFormula_defined :
    ℒₛₑₜ-function₅[V] successorSectionColumn via piOneSuccessorSectionColumnFormula :=
  ⟨fun v ↦ by simp [piOneSuccessorSectionColumnFormula]⟩
instance piOneSuccessorLiftColumnFormula_defined :
    ℒₛₑₜ-function₅[V] successorLiftColumn via piOneSuccessorLiftColumnFormula :=
  ⟨fun v ↦ by simp [piOneSuccessorLiftColumnFormula]⟩

end ZFVP
