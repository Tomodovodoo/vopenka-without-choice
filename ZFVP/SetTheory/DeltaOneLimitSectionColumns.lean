import ZFVP.SetTheory.DeltaOneSectionThread
import ZFVP.SetTheory.ForcingLimitColumns

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sectionThreadRow (φ : SetTheorySemisentence 6) : SetTheorySemisentence 6 :=
  “y p θ π E i. !φ y θ π E i p”

theorem sectionThreadRow_levy {pol : LevyPolarity} {k : ℕ} {φ : SetTheorySemisentence 6}
    (h : IsLevyFormula pol k φ) : IsLevyFormula pol k (sectionThreadRow φ) := h.subst _

def sigmaOneThreadSectionFormula : SetTheorySemisentence 6 :=
  “G θ P π E i. ∃ A, !boundedValueFormula A P i ∧
    !(graphAssemblyFormula (sectionThreadRow sigmaOneSectionThreadFormula)) G A θ π E i”

def piOneThreadSectionFormula : SetTheorySemisentence 6 :=
  “G θ P π E i. ∀ A, !boundedValueFormula A P i →
    !(graphAssemblyFormula (sectionThreadRow piOneSectionThreadFormula)) G A θ π E i”

theorem sigmaOneThreadSectionFormula_sigmaOne : IsSigmaFormula 1 sigmaOneThreadSectionFormula :=
  .exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    ((graphAssemblyFormula_levy (sectionThreadRow_levy sigmaOneSectionThreadFormula_sigmaOne)).subst _))

theorem piOneThreadSectionFormula_piOne : IsPiFormula 1 piOneThreadSectionFormula :=
  .all (.or (.bounded (boundedValueFormula_bounded.subst _).neg)
    ((graphAssemblyFormula_levy (sectionThreadRow_levy piOneSectionThreadFormula_piOne)).subst _))

def threadSectionRow (φ : SetTheorySemisentence 6) : SetTheorySemisentence 6 :=
  “y i θ P π E. !φ y θ P π E i”

theorem threadSectionRow_levy {pol : LevyPolarity} {k : ℕ} {φ : SetTheorySemisentence 6}
    (h : IsLevyFormula pol k φ) : IsLevyFormula pol k (threadSectionRow φ) := h.subst _

def sigmaOneLimitSectionColumnFormula : SetTheorySemisentence 5 :=
  “G θ P π E. !(graphAssemblyFormula (threadSectionRow sigmaOneThreadSectionFormula)) G θ θ P π E”

def piOneLimitSectionColumnFormula : SetTheorySemisentence 5 :=
  “G θ P π E. !(graphAssemblyFormula (threadSectionRow piOneThreadSectionFormula)) G θ θ P π E”

theorem sigmaOneLimitSectionColumnFormula_sigmaOne : IsSigmaFormula 1 sigmaOneLimitSectionColumnFormula :=
  (graphAssemblyFormula_levy (threadSectionRow_levy sigmaOneThreadSectionFormula_sigmaOne)).subst _

theorem piOneLimitSectionColumnFormula_piOne : IsPiFormula 1 piOneLimitSectionColumnFormula :=
  (graphAssemblyFormula_levy (threadSectionRow_levy piOneThreadSectionFormula_piOne)).subst _

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sectionThreadRow_graph {φ : SetTheorySemisentence 6}
    [ℒₛₑₜ-function₅[V] forcingSectionThread via φ] (G θ P π E i : V) :
    (graphAssemblyFormula (sectionThreadRow φ)).Evalb ![G, P ‘ i, θ, π, E, i] ↔
      G = forcingThreadSection θ P π E i := by
  exact eval_graphAssemblyFormula (sectionThreadRow φ) G (P ‘ i) ![θ, π, E, i]
    (forcingSectionThread θ π E i) _ (fun p _ y ↦ by simp [sectionThreadRow])

instance sigmaOneThreadSectionFormula_defined : ℒₛₑₜ-function₅[V] forcingThreadSection via sigmaOneThreadSectionFormula :=
  ⟨fun v ↦ by
    have he := eval_sectionThreadRow_graph (φ := sigmaOneSectionThreadFormula)
      (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
    simp only [Semiformula.Evalb] at he
    simpa [sigmaOneThreadSectionFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def] using he⟩

instance piOneThreadSectionFormula_defined : ℒₛₑₜ-function₅[V] forcingThreadSection via piOneThreadSectionFormula :=
  ⟨fun v ↦ by
    have he := eval_sectionThreadRow_graph (φ := piOneSectionThreadFormula)
      (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
    simp only [Semiformula.Evalb] at he
    simpa [piOneThreadSectionFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def] using he⟩

theorem eval_threadSectionRow_graph {φ : SetTheorySemisentence 6}
    [ℒₛₑₜ-function₅[V] forcingThreadSection via φ] (G θ P π E : V) :
    (graphAssemblyFormula (threadSectionRow φ)).Evalb ![G, θ, θ, P, π, E] ↔
      G = forcingLimitSectionColumn θ P π E := by
  exact eval_graphAssemblyFormula (threadSectionRow φ) G θ ![θ, P, π, E]
    (forcingThreadSection θ P π E) _ (fun i _ y ↦ by simp [threadSectionRow])

instance sigmaOneLimitSectionColumnFormula_defined :
    ℒₛₑₜ-function₄[V] forcingLimitSectionColumn via sigmaOneLimitSectionColumnFormula :=
  ⟨fun v ↦ by
    have he := eval_threadSectionRow_graph (φ := sigmaOneThreadSectionFormula)
      (v 0) (v 1) (v 2) (v 3) (v 4)
    simp only [Semiformula.Evalb] at he
    simpa [sigmaOneLimitSectionColumnFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def] using he⟩

instance piOneLimitSectionColumnFormula_defined :
    ℒₛₑₜ-function₄[V] forcingLimitSectionColumn via piOneLimitSectionColumnFormula :=
  ⟨fun v ↦ by
    have he := eval_threadSectionRow_graph (φ := piOneThreadSectionFormula)
      (v 0) (v 1) (v 2) (v 3) (v 4)
    simp only [Semiformula.Evalb] at he
    simpa [piOneLimitSectionColumnFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def] using he⟩

end ZFVP
