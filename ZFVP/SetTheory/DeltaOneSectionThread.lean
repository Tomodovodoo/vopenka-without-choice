import ZFVP.SetTheory.LevyGraphAssembly
import ZFVP.SetTheory.BoundedValue
import ZFVP.SetTheory.ForcingSectionThread

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sectionValueTestFormula : SetTheorySemisentence 6 :=
  “y i k p c d. (i ∈ k ∧ !boundedValueFormula y c p) ∨
    (i ∉ k ∧ !boundedValueFormula y d p)”

theorem sectionValueTestFormula_bounded : IsBoundedSetFormula sectionValueTestFormula :=
  .or (.and (.rel _ _) (boundedValueFormula_bounded.subst _))
    (.and (.nrel _ _) (boundedValueFormula_bounded.subst _))

def sigmaOneSectionValueFormula : SetTheorySemisentence 6 :=
  “y i π E k p. ∃ a, !boundedKpairFormula a i k ∧ ∃ b, !boundedKpairFormula b k i ∧
    ∃ c, !boundedValueFormula c π a ∧ ∃ d, !boundedValueFormula d E b ∧
    !sectionValueTestFormula y i k p c d”

def piOneSectionValueFormula : SetTheorySemisentence 6 :=
  “y i π E k p. ∀ a, !boundedKpairFormula a i k → ∀ b, !boundedKpairFormula b k i →
    ∀ c, !boundedValueFormula c π a → ∀ d, !boundedValueFormula d E b →
    !sectionValueTestFormula y i k p c d”

theorem sigmaOneSectionValueFormula_sigmaOne : IsSigmaFormula 1 sigmaOneSectionValueFormula :=
  .exs (.and (.bounded (boundedKpairFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedKpairFormula_bounded.subst _))
      (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
        (.exs (.bounded (.and (boundedValueFormula_bounded.subst _)
          (sectionValueTestFormula_bounded.subst _)))))))))

theorem piOneSectionValueFormula_piOne : IsPiFormula 1 piOneSectionValueFormula :=
  .all (.or (.bounded (boundedKpairFormula_bounded.subst _).neg)
    (.all (.or (.bounded (boundedKpairFormula_bounded.subst _).neg)
      (.all (.or (.bounded (boundedValueFormula_bounded.subst _).neg)
        (.all (.bounded (.or (boundedValueFormula_bounded.subst _).neg
          (sectionValueTestFormula_bounded.subst _)))))))))

def sigmaOneSectionThreadFormula : SetTheorySemisentence 6 := graphAssemblyFormula sigmaOneSectionValueFormula

def piOneSectionThreadFormula : SetTheorySemisentence 6 := graphAssemblyFormula piOneSectionValueFormula

theorem sigmaOneSectionThreadFormula_sigmaOne : IsSigmaFormula 1 sigmaOneSectionThreadFormula :=
  graphAssemblyFormula_levy sigmaOneSectionValueFormula_sigmaOne

theorem piOneSectionThreadFormula_piOne : IsPiFormula 1 piOneSectionThreadFormula :=
  graphAssemblyFormula_levy piOneSectionValueFormula_piOne

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sigmaOneSectionValueFormula_defined : Defined
    (fun v : Fin 6 → V ↦ v 0 = forcingSectionValue (v 2) (v 3) (v 4) (v 5) (v 1))
    sigmaOneSectionValueFormula :=
  ⟨fun v ↦ by
    classical
    by_cases h : v 1 ∈ v 4 <;>
      simp [sigmaOneSectionValueFormula, sectionValueTestFormula, forcingSectionValue, h]⟩

instance piOneSectionValueFormula_defined : Defined
    (fun v : Fin 6 → V ↦ v 0 = forcingSectionValue (v 2) (v 3) (v 4) (v 5) (v 1))
    piOneSectionValueFormula :=
  ⟨fun v ↦ by
    classical
    by_cases h : v 1 ∈ v 4 <;>
      simp [piOneSectionValueFormula, sectionValueTestFormula, forcingSectionValue, h]⟩

theorem eval_sigmaOneSectionThreadFormula (G θ π E k p : V) :
    sigmaOneSectionThreadFormula.Evalb ![G, θ, π, E, k, p] ↔ G = forcingSectionThread θ π E k p := by
  exact eval_graphAssemblyFormula sigmaOneSectionValueFormula G θ ![π, E, k, p]
    (forcingSectionValue π E k p) _ (fun i _ y ↦ by simp)

theorem eval_piOneSectionThreadFormula (G θ π E k p : V) :
    piOneSectionThreadFormula.Evalb ![G, θ, π, E, k, p] ↔ G = forcingSectionThread θ π E k p := by
  exact eval_graphAssemblyFormula piOneSectionValueFormula G θ ![π, E, k, p]
    (forcingSectionValue π E k p) _ (fun i _ y ↦ by simp)

instance sigmaOneSectionThreadFormula_defined : ℒₛₑₜ-function₅[V] forcingSectionThread via sigmaOneSectionThreadFormula :=
  ⟨fun v ↦ by
    change sigmaOneSectionThreadFormula.Evalb v ↔ v 0 = forcingSectionThread (v 1) (v 2) (v 3) (v 4) (v 5)
    have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5] := by
      funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i) i) i) i) i
    exact (Iff.of_eq (congrArg (fun w ↦ sigmaOneSectionThreadFormula.Evalb w) hv)).trans
      (eval_sigmaOneSectionThreadFormula (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))⟩

instance piOneSectionThreadFormula_defined : ℒₛₑₜ-function₅[V] forcingSectionThread via piOneSectionThreadFormula :=
  ⟨fun v ↦ by
    change piOneSectionThreadFormula.Evalb v ↔ v 0 = forcingSectionThread (v 1) (v 2) (v 3) (v 4) (v 5)
    have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5] := by
      funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i) i) i) i) i
    exact (Iff.of_eq (congrArg (fun w ↦ piOneSectionThreadFormula.Evalb w) hv)).trans
      (eval_piOneSectionThreadFormula (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))⟩

end ZFVP
