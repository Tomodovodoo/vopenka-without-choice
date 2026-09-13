import ZFVP.SetTheory.Cn
import ZFVP.Syntax.UniformBoundedCodes

/-! The strengthened Sigma-one reflection of Spoerl, Definition 20.
The bounded formulas are internal codes, including nonstandard codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def binaryTupleFormula : SetTheorySemisentence 3 :=
  f“t a b. t = !assignmentPrependFormula (!(numeralFormula 1))
    (!assignmentPrependFormula (!isEmpty) (!isEmpty) b) a”

def rankFunctionClosedFormula : SetTheorySemisentence 2 :=
  f“α b. !function.dfn b (!hierarchyFormula α) ⊆ b”

def starReflectionWitnessFormula : SetTheorySemisentence 4 :=
  f“α φ a b. !rankFunctionClosedFormula α b ∧
    !boundedTruthFormula (!(numeralFormula 2)) φ (!binaryTupleFormula a b)”

def sigmaOneStarCorrectFormula : SetTheorySemisentence 1 :=
  f“γ. !(cnFormula 1) γ ∧ ∀ α ∈ γ, ∀ a ∈ !hierarchyFormula γ, ∀ φ,
    !isBoundedFormulaCodeFormula (!(numeralFormula 2)) φ →
    (∃ b, !starReflectionWitnessFormula α φ a b) →
    ∃ b ∈ !hierarchyFormula γ, !starReflectionWitnessFormula α φ a b”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsRankFunctionClosed (α b : V) : Prop := b ^ hierarchy α ⊆ b

def StarReflectionWitness (α φ a b : V) : Prop :=
  IsRankFunctionClosed α b ∧ BoundedTruth 2 φ (standardTuple ![a, b])

def IsSigmaOneStarCorrect (γ : V) : Prop :=
  Cn 1 γ ∧ ∀ α ∈ γ, ∀ a ∈ hierarchy γ, ∀ φ, IsBoundedFormulaCode 2 φ →
    (∃ b, StarReflectionWitness α φ a b) →
    ∃ b ∈ hierarchy γ, StarReflectionWitness α φ a b

instance binaryTupleFormula_defined :
    ℒₛₑₜ-function₂[V] (fun a b ↦ standardTuple ![a, b]) via binaryTupleFormula :=
  ⟨fun v ↦ by simp [binaryTupleFormula, standardTuple, zero_def]⟩

instance rankFunctionClosedFormula_defined :
    ℒₛₑₜ-relation[V] IsRankFunctionClosed via rankFunctionClosedFormula :=
  ⟨fun v ↦ by simp [rankFunctionClosedFormula, IsRankFunctionClosed]⟩

instance starReflectionWitnessFormula_defined :
    ℒₛₑₜ-relation₄[V] StarReflectionWitness via starReflectionWitnessFormula :=
  ⟨fun v ↦ by simp [starReflectionWitnessFormula, StarReflectionWitness]⟩

instance sigmaOneStarCorrectFormula_defined :
    ℒₛₑₜ-predicate[V] IsSigmaOneStarCorrect via sigmaOneStarCorrectFormula :=
  ⟨fun v ↦ by simp [sigmaOneStarCorrectFormula, IsSigmaOneStarCorrect]⟩

instance sigmaOneStarCorrect_definable : ℒₛₑₜ-predicate[V] IsSigmaOneStarCorrect :=
  sigmaOneStarCorrectFormula_defined.to_definable

theorem IsSigmaOneStarCorrect.reflect {γ α a : V} (hγ : IsSigmaOneStarCorrect γ)
    (hα : α ∈ γ) (ha : a ∈ hierarchy γ) {φ : SetTheorySemisentence 2}
    (hφ : IsBoundedSetFormula φ)
    (hex : ∃ b, IsRankFunctionClosed α b ∧ φ.Evalb ![a, b]) :
    ∃ b ∈ hierarchy γ, IsRankFunctionClosed α b ∧ φ.Evalb ![a, b] := by
  obtain ⟨b, hb, hc, ht⟩ := hγ.2 α hα a ha (encodeMembershipFormula φ)
    hφ.encode (by
      obtain ⟨b, hc, ht⟩ := hex
      exact ⟨b, hc, (boundedTruth_correct hφ ![a, b]).mpr ht⟩)
  exact ⟨b, hb, hc, (boundedTruth_correct hφ ![a, b]).mp ht⟩

end ZFVP

