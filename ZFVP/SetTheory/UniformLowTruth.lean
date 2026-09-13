import ZFVP.SetTheory.LevelOneTruth
import ZFVP.Syntax.UniformSatisfaction

/-! Fixed parameter-free definitions of the bounded and level-one truth evaluators.
These definitions do not yet certify their Levy complexity. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def equalityTupleRelationFormula : SetTheorySemisentence 2 :=
  f“D A. ∀ s, s ∈ D ↔ s ∈ !function.dfn A (!(numeralFormula 2)) ∧
    !value.dfn s (!isEmpty) = !value.dfn s (!(numeralFormula 1))”

def membershipTupleRelationFormula : SetTheorySemisentence 2 :=
  f“D A. ∀ s, s ∈ D ↔ s ∈ !function.dfn A (!(numeralFormula 2)) ∧
    !value.dfn s (!isEmpty) ∈ !value.dfn s (!(numeralFormula 1))”

def membershipLanguageCodeFormula : SetTheorySemisentence 1 :=
  f“L. L = !languageCodeFormula (!isEmpty) (!(numeralFormula 2))
    (!constantGraphFormula (!isEmpty) (!(numeralFormula 2)))
    (!constantGraphFormula (!(numeralFormula 2)) (!(numeralFormula 2)))”

def membershipInterpretationFormula : SetTheorySemisentence 3 :=
  f“D A r. (r = !isEmpty ∧ D = !equalityTupleRelationFormula A) ∨
    (r ≠ !isEmpty ∧ D = !membershipTupleRelationFormula A)”

def membershipRelationTableFormula : SetTheorySemisentence 2 :=
  f“RI A. ∀ p, p ∈ RI ↔ ∃ r ∈ !(numeralFormula 2),
    p = !kpair.dfn r (!membershipInterpretationFormula A r)”

def membershipStructureCodeFormula : SetTheorySemisentence 2 :=
  f“M A. M = !structureCodeFormula A (!constantGraphFormula (!isEmpty) (!isEmpty))
    (!membershipRelationTableFormula A)”

def transitiveClosureFormula : SetTheorySemisentence 2 :=
  f“T X. !IsTransitive.dfn T ∧ X ⊆ T ∧ ∀ U, !IsTransitive.dfn U → X ⊆ U → T ⊆ U”

def boundedTruthDomainFormula : SetTheorySemisentence 2 :=
  f“A b. A = !transitiveClosureFormula (!singleton.dfn (!range.dfn b))”

def membershipSatisfiesFormula : SetTheorySemisentence 4 :=
  f“A n φ b. b ∈ !value.dfn
    (!satisfactionGraphFormula (!membershipLanguageCodeFormula) (!isEmpty)
      (!membershipStructureCodeFormula A) (!isEmpty)) (!kpair.dfn n φ)”

def boundedTruthFormula : SetTheorySemisentence 3 :=
  f“n φ b. !membershipSatisfiesFormula (!boundedTruthDomainFormula b) n φ b”

def sigmaOneTruthFormula : SetTheorySemisentence 3 :=
  f“n φ b. ∃ A, !IsTransitive.dfn A ∧ !isNonempty A ∧ b ∈ !function.dfn A n ∧
    !membershipSatisfiesFormula A n φ b”

def piOneTruthFormula : SetTheorySemisentence 3 :=
  f“n φ b. ∀ A, !IsTransitive.dfn A → !isNonempty A → b ∈ !function.dfn A n →
    !membershipSatisfiesFormula A n φ b”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance equalityTupleRelationFormula_defined :
    ℒₛₑₜ-function₁[V] equalityRelation via equalityTupleRelationFormula := ⟨fun v ↦ by
  change equalityTupleRelationFormula.Evalb v ↔ v 0 = equalityRelation (v 1)
  rw [mem_ext_iff]
  simp [equalityTupleRelationFormula, mem_equalityRelation_iff, zero_def]⟩

instance membershipTupleRelationFormula_defined :
    ℒₛₑₜ-function₁[V] membershipTupleRelation via membershipTupleRelationFormula := ⟨fun v ↦ by
  change membershipTupleRelationFormula.Evalb v ↔ v 0 = membershipTupleRelation (v 1)
  rw [mem_ext_iff]
  simp [membershipTupleRelationFormula, mem_membershipTupleRelation_iff, zero_def]⟩

instance membershipLanguageCodeFormula_defined :
    ℒₛₑₜ-function₀[V] membershipLanguageCode via membershipLanguageCodeFormula :=
  ⟨fun v ↦ by simp [membershipLanguageCodeFormula, membershipLanguageCode]⟩

instance membershipInterpretationFormula_defined :
    ℒₛₑₜ-function₂[V] membershipInterpretation via membershipInterpretationFormula := ⟨fun v ↦ by
  change membershipInterpretationFormula.Evalb v ↔ v 0 = membershipInterpretation (v 1) (v 2)
  simp only [membershipInterpretationFormula, LogicalConnective.HomClass.map_or]
  unfold membershipInterpretation
  split <;> simp_all [zero_def]⟩

instance membershipRelationTableFormula_defined :
    ℒₛₑₜ-function₁[V] (fun A ↦ definableGraph (2 : V) (membershipInterpretation A) (by definability))
      via membershipRelationTableFormula := ⟨fun v ↦ by
  change membershipRelationTableFormula.Evalb v ↔
    v 0 = definableGraph (2 : V) (membershipInterpretation (v 1)) _
  rw [mem_ext_iff]
  simp [membershipRelationTableFormula, mem_definableGraph_iff]⟩

instance membershipStructureCodeFormula_defined :
    ℒₛₑₜ-function₁[V] membershipStructureCode via membershipStructureCodeFormula :=
  ⟨fun v ↦ by
    simp [membershipStructureCodeFormula, membershipStructureCode]
    constructor
    · intro h
      exact h _ (by intro x hx; exact congrArg (structureCode (v 1) (constantGraph ∅ ∅)) hx.symm)
    · intro h x hx
      exact h.trans (hx _ rfl).symm⟩

instance transitiveClosureFormula_defined :
    ℒₛₑₜ-function₁[V] transitiveClosure via transitiveClosureFormula := ⟨fun v ↦ by
  change transitiveClosureFormula.Evalb v ↔ v 0 = transitiveClosure (v 1)
  rw [transitiveClosure_characterization]
  simp [transitiveClosureFormula]⟩

instance boundedTruthDomainFormula_defined :
    ℒₛₑₜ-function₁[V] boundedTruthDomain via boundedTruthDomainFormula :=
  ⟨fun v ↦ by simp [boundedTruthDomainFormula, boundedTruthDomain]⟩

instance membershipSatisfiesFormula_defined :
    ℒₛₑₜ-relation₄[V] MembershipSatisfies via membershipSatisfiesFormula :=
  ⟨fun v ↦ by simp [membershipSatisfiesFormula, MembershipSatisfies, membershipSatisfactionGraph]⟩

instance boundedTruthFormula_defined : ℒₛₑₜ-relation₃[V] BoundedTruth via boundedTruthFormula :=
  ⟨fun v ↦ by simp [boundedTruthFormula, BoundedTruth, MembershipSatisfies, membershipSatisfactionGraph, Satisfies]⟩

instance sigmaOneTruthFormula_defined : ℒₛₑₜ-relation₃[V] SigmaOneTruth via sigmaOneTruthFormula :=
  ⟨fun v ↦ by simp [sigmaOneTruthFormula, SigmaOneTruth]⟩

instance piOneTruthFormula_defined : ℒₛₑₜ-relation₃[V] PiOneTruth via piOneTruthFormula :=
  ⟨fun v ↦ by simp [piOneTruthFormula, PiOneTruth]⟩

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_transitiveClosure (j : ElementaryMap V W) (X : V) :
    j (transitiveClosure X) = transitiveClosure (j X) :=
  j.map_definedFunction₁ transitiveClosureFormula transitiveClosure transitiveClosure X

theorem map_membershipStructureCode (j : ElementaryMap V W) (A : V) :
    j (membershipStructureCode A) = membershipStructureCode (j A) :=
  j.map_definedFunction₁ membershipStructureCodeFormula membershipStructureCode membershipStructureCode A

theorem map_boundedTruth_iff (j : ElementaryMap V W) (n φ b : V) :
    BoundedTruth (j n) (j φ) (j b) ↔ BoundedTruth n φ b :=
  (j.map_defined boundedTruthFormula (fun v ↦ BoundedTruth (v 0) (v 1) (v 2))
    (fun v ↦ BoundedTruth (v 0) (v 1) (v 2)) ![n, φ, b]).symm

theorem map_sigmaOneTruth_iff (j : ElementaryMap V W) (n φ b : V) :
    SigmaOneTruth (j n) (j φ) (j b) ↔ SigmaOneTruth n φ b :=
  (j.map_defined sigmaOneTruthFormula (fun v ↦ SigmaOneTruth (v 0) (v 1) (v 2))
    (fun v ↦ SigmaOneTruth (v 0) (v 1) (v 2)) ![n, φ, b]).symm

theorem map_piOneTruth_iff (j : ElementaryMap V W) (n φ b : V) :
    PiOneTruth (j n) (j φ) (j b) ↔ PiOneTruth n φ b :=
  (j.map_defined piOneTruthFormula (fun v ↦ PiOneTruth (v 0) (v 1) (v 2))
    (fun v ↦ PiOneTruth (v 0) (v 1) (v 2)) ![n, φ, b]).symm

end ElementaryMap
end ZFVP


