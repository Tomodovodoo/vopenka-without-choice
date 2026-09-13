import ZFVP.ModelTheory.DeltaOneTwoStepConditions
import ZFVP.ModelTheory.DeltaOneSuccessorMaps
import ZFVP.ModelTheory.ForcingInverseTwoStepUniform
import ZFVP.SetTheory.DeltaOneRelationComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def twoStepSectionValueCertificate : SetTheorySemisentence 3 := “y p t. !boundedKpairFormula y p t”
def composeProjectionColumnRow : SetTheorySemisentence 4 :=
  “y i ρ v. ∃ g, !boundedValueFormula g ρ i ∧ !sigmaOneRelationCompositionFormula y v g”
def composeSectionColumnRow : SetTheorySemisentence 4 :=
  “y i F e. ∃ g, !boundedValueFormula g F i ∧ !sigmaOneRelationCompositionFormula y g e”
def twoStepLiftColumnRow : SetTheorySemisentence 5 :=
  “y i D P M. ∃ A, !boundedValueFormula A P i ∧ ∃ L, !boundedValueFormula L M i ∧
    !sigmaOneSuccessorLiftFormula y D A L”

def sigmaOneTwoStepProjectionFormula : SetTheorySemisentence 5 :=
  “G P R Q t. ∃ C, !sigmaOneTwoStepConditionSetFormula C P R Q t ∧
    !(graphAssemblyFormula sigmaOnePairFirstFormula) G C”
def sigmaOneTwoStepSectionFormula : SetTheorySemisentence 3 := graphAssemblyFormula twoStepSectionValueCertificate
def sigmaOneComposeProjectionColumnFormula : SetTheorySemisentence 4 := graphAssemblyFormula composeProjectionColumnRow
def sigmaOneComposeSectionColumnFormula : SetTheorySemisentence 4 := graphAssemblyFormula composeSectionColumnRow
def sigmaOneTwoStepLiftColumnFormula : SetTheorySemisentence 5 := graphAssemblyFormula twoStepLiftColumnRow

theorem sigmaOneTwoStepProjectionFormula_sigmaOne : IsSigmaFormula 1 sigmaOneTwoStepProjectionFormula :=
  .exs (.and (sigmaOneTwoStepConditionSetFormula_sigmaOne.subst _)
    ((graphAssemblyFormula_levy sigmaOnePairFirstFormula_sigmaOne).subst _))
theorem sigmaOneTwoStepSectionFormula_sigmaOne : IsSigmaFormula 1 sigmaOneTwoStepSectionFormula :=
  graphAssemblyFormula_levy (.bounded (boundedKpairFormula_bounded.subst _))
theorem sigmaOneComposeProjectionColumnFormula_sigmaOne : IsSigmaFormula 1 sigmaOneComposeProjectionColumnFormula :=
  graphAssemblyFormula_levy (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    (sigmaOneRelationCompositionFormula_sigmaOne.subst _)))
theorem sigmaOneComposeSectionColumnFormula_sigmaOne : IsSigmaFormula 1 sigmaOneComposeSectionColumnFormula :=
  graphAssemblyFormula_levy (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    (sigmaOneRelationCompositionFormula_sigmaOne.subst _)))
theorem sigmaOneTwoStepLiftColumnFormula_sigmaOne : IsSigmaFormula 1 sigmaOneTwoStepLiftColumnFormula :=
  graphAssemblyFormula_levy (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedValueFormula_bounded.subst _)) (sigmaOneSuccessorLiftFormula_sigmaOne.subst _)))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_pairFirstGraphCertificate (G C : V) :
    (graphAssemblyFormula sigmaOnePairFirstFormula).Evalb ![G, C] ↔
      G = definableGraph C kpair.π₁ (by definability) :=
  eval_graphAssemblyFormula sigmaOnePairFirstFormula G C ![] kpair.π₁ (by definability)
    (fun a _ y ↦ by simp)

theorem eval_sigmaOneTwoStepProjectionFormula (G P R Q t : V) :
    sigmaOneTwoStepProjectionFormula.Evalb ![G, P, R, Q, t] ↔ G = twoStepProjection P R Q t := by
  have he := eval_pairFirstGraphCertificate (V := V)
  simp only [Semiformula.Evalb] at he
  simp [sigmaOneTwoStepProjectionFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he, twoStepProjection]

theorem eval_sigmaOneTwoStepSectionFormula (G P t : V) :
    sigmaOneTwoStepSectionFormula.Evalb ![G, P, t] ↔ G = twoStepSection P t := by
  apply eval_graphAssemblyFormula twoStepSectionValueCertificate G P ![t] (fun p ↦ ⟨p, t⟩ₖ) (by definability)
  intro p _ y
  simp [twoStepSectionValueCertificate]

theorem eval_sigmaOneComposeProjectionColumnFormula (G θ ρ v : V) :
    sigmaOneComposeProjectionColumnFormula.Evalb ![G, θ, ρ, v] ↔ G = forcingComposeProjectionColumn θ ρ v := by
  apply eval_graphAssemblyFormula composeProjectionColumnRow G θ ![ρ, v]
    (fun i ↦ compose v (ρ ‘ i)) (by definability)
  intro i _ y
  simp [composeProjectionColumnRow]

theorem eval_sigmaOneComposeSectionColumnFormula (G θ F e : V) :
    sigmaOneComposeSectionColumnFormula.Evalb ![G, θ, F, e] ↔ G = forcingComposeSectionColumn θ F e := by
  apply eval_graphAssemblyFormula composeSectionColumnRow G θ ![F, e]
    (fun i ↦ compose (F ‘ i) e) (by definability)
  intro i _ y
  simp [composeSectionColumnRow]

theorem eval_sigmaOneTwoStepLiftColumnFormula (G θ D P M : V) :
    sigmaOneTwoStepLiftColumnFormula.Evalb ![G, θ, D, P, M] ↔ G = forcingTwoStepLiftColumn θ D P M := by
  apply eval_graphAssemblyFormula twoStepLiftColumnRow G θ ![D, P, M]
    (fun i ↦ successorForcingLift D (P ‘ i) (M ‘ i)) (by definability)
  intro i _ y
  simp [twoStepLiftColumnRow]

instance sigmaOneTwoStepProjectionFormula_defined :
    ℒₛₑₜ-function₄[V] twoStepProjection via sigmaOneTwoStepProjectionFormula :=
  ⟨fun v ↦ by
    have hv : v = ![v 0, v 1, v 2, v 3, v 4] := by funext i; fin_cases i <;> rfl
    change sigmaOneTwoStepProjectionFormula.Evalb v ↔ _
    rw [hv]
    exact eval_sigmaOneTwoStepProjectionFormula _ _ _ _ _⟩

def piOneTwoStepProjectionFormula : SetTheorySemisentence 5 :=
  “G P R Q t. ∀ H, !sigmaOneTwoStepProjectionFormula H P R Q t → G = H”

theorem piOneTwoStepProjectionFormula_piOne : IsPiFormula 1 piOneTwoStepProjectionFormula :=
  .all (.or (sigmaOneTwoStepProjectionFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))

instance piOneTwoStepProjectionFormula_defined :
    ℒₛₑₜ-function₄[V] twoStepProjection via piOneTwoStepProjectionFormula :=
  ⟨fun v ↦ by simp [piOneTwoStepProjectionFormula]⟩

instance sigmaOneTwoStepSectionFormula_defined :
    ℒₛₑₜ-function₂[V] twoStepSection via sigmaOneTwoStepSectionFormula :=
  ⟨fun v ↦ by
    have hv : v = ![v 0, v 1, v 2] := by funext i; fin_cases i <;> rfl
    change sigmaOneTwoStepSectionFormula.Evalb v ↔ _
    rw [hv]
    exact eval_sigmaOneTwoStepSectionFormula _ _ _⟩

def piOneTwoStepSectionFormula : SetTheorySemisentence 3 :=
  “G P t. ∀ H, !sigmaOneTwoStepSectionFormula H P t → G = H”

theorem piOneTwoStepSectionFormula_piOne : IsPiFormula 1 piOneTwoStepSectionFormula :=
  .all (.or (sigmaOneTwoStepSectionFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))

instance piOneTwoStepSectionFormula_defined :
    ℒₛₑₜ-function₂[V] twoStepSection via piOneTwoStepSectionFormula :=
  ⟨fun v ↦ by simp [piOneTwoStepSectionFormula]⟩

instance sigmaOneComposeProjectionColumnFormula_defined :
    ℒₛₑₜ-function₃[V] forcingComposeProjectionColumn via sigmaOneComposeProjectionColumnFormula :=
  ⟨fun v ↦ by
    have hv : v = ![v 0, v 1, v 2, v 3] := by funext i; fin_cases i <;> rfl
    change sigmaOneComposeProjectionColumnFormula.Evalb v ↔ _
    rw [hv]
    exact eval_sigmaOneComposeProjectionColumnFormula _ _ _ _⟩

def piOneComposeProjectionColumnFormula : SetTheorySemisentence 4 :=
  “G θ ρ v. ∀ H, !sigmaOneComposeProjectionColumnFormula H θ ρ v → G = H”

theorem piOneComposeProjectionColumnFormula_piOne : IsPiFormula 1 piOneComposeProjectionColumnFormula :=
  .all (.or (sigmaOneComposeProjectionColumnFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))

instance piOneComposeProjectionColumnFormula_defined :
    ℒₛₑₜ-function₃[V] forcingComposeProjectionColumn via piOneComposeProjectionColumnFormula :=
  ⟨fun v ↦ by simp [piOneComposeProjectionColumnFormula]⟩

instance sigmaOneComposeSectionColumnFormula_defined :
    ℒₛₑₜ-function₃[V] forcingComposeSectionColumn via sigmaOneComposeSectionColumnFormula :=
  ⟨fun v ↦ by
    have hv : v = ![v 0, v 1, v 2, v 3] := by funext i; fin_cases i <;> rfl
    change sigmaOneComposeSectionColumnFormula.Evalb v ↔ _
    rw [hv]
    exact eval_sigmaOneComposeSectionColumnFormula _ _ _ _⟩

def piOneComposeSectionColumnFormula : SetTheorySemisentence 4 :=
  “G θ F e. ∀ H, !sigmaOneComposeSectionColumnFormula H θ F e → G = H”

theorem piOneComposeSectionColumnFormula_piOne : IsPiFormula 1 piOneComposeSectionColumnFormula :=
  .all (.or (sigmaOneComposeSectionColumnFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))

instance piOneComposeSectionColumnFormula_defined :
    ℒₛₑₜ-function₃[V] forcingComposeSectionColumn via piOneComposeSectionColumnFormula :=
  ⟨fun v ↦ by simp [piOneComposeSectionColumnFormula]⟩

instance sigmaOneTwoStepLiftColumnFormula_defined :
    ℒₛₑₜ-function₄[V] forcingTwoStepLiftColumn via sigmaOneTwoStepLiftColumnFormula :=
  ⟨fun v ↦ by
    have hv : v = ![v 0, v 1, v 2, v 3, v 4] := by funext i; fin_cases i <;> rfl
    change sigmaOneTwoStepLiftColumnFormula.Evalb v ↔ _
    rw [hv]
    exact eval_sigmaOneTwoStepLiftColumnFormula _ _ _ _ _⟩

def piOneTwoStepLiftColumnFormula : SetTheorySemisentence 5 :=
  “G θ D P M. ∀ H, !sigmaOneTwoStepLiftColumnFormula H θ D P M → G = H”

theorem piOneTwoStepLiftColumnFormula_piOne : IsPiFormula 1 piOneTwoStepLiftColumnFormula :=
  .all (.or (sigmaOneTwoStepLiftColumnFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))

instance piOneTwoStepLiftColumnFormula_defined :
    ℒₛₑₜ-function₄[V] forcingTwoStepLiftColumn via piOneTwoStepLiftColumnFormula :=
  ⟨fun v ↦ by simp [piOneTwoStepLiftColumnFormula]⟩

end ZFVP
