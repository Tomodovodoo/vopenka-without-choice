import ZFVP.ModelTheory.BinaryRelationStructure
import ZFVP.ModelTheory.UniformCodes
import ZFVP.Syntax.UniformZFVPAxioms
import ZFVP.ModelTheory.CodedZFModel

/-! Uniform formulas for arbitrary binary structures and the full internal ZF scheme. -/
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def binaryTupleRelationFormula : SetTheorySemisentence 3 :=
  f“R D E. ∀ s, s ∈ R ↔ s ∈ !function.dfn D (!(numeralFormula 2)) ∧
    !kpair.dfn (!value.dfn s (!isEmpty)) (!value.dfn s (!(numeralFormula 1))) ∈ E”

def binaryRelationInterpretationFormula : SetTheorySemisentence 4 :=
  f“R D E r. (r = !isEmpty ∧ R = !equalityTupleRelationFormula D) ∨
    (r ≠ !isEmpty ∧ R = !binaryTupleRelationFormula D E)”

def binaryRelationInterpretationsFormula : SetTheorySemisentence 3 :=
  f“G D E. ∀ p, p ∈ G ↔ ∃ r ∈ !(numeralFormula 2),
    p = !kpair.dfn r (!binaryRelationInterpretationFormula D E r)”

def binaryRelationStructureCodeFormula : SetTheorySemisentence 3 :=
  f“M D E. M = !structureCodeFormula D (!constantGraphFormula (!isEmpty) (!isEmpty))
    (!binaryRelationInterpretationsFormula D E)”

def isCodedZFModelFormula : SetTheorySemisentence 1 :=
  f“M. !satisfiesCodedOpenTheoryFormula (!membershipLanguageCodeFormula) M (!zfOpenAxiomCodesFormula)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance binaryTupleRelationFormula_defined :
    ℒₛₑₜ-function₂[V] binaryTupleRelation via binaryTupleRelationFormula :=
  ⟨fun v ↦ by
    change binaryTupleRelationFormula.Evalb v ↔ v 0 = binaryTupleRelation (v 1) (v 2)
    rw [mem_ext_iff]
    simp [binaryTupleRelationFormula, binaryTupleRelation, zero_def]⟩

instance binaryRelationInterpretationFormula_defined :
    ℒₛₑₜ-function₃[V] binaryRelationInterpretation via binaryRelationInterpretationFormula :=
  ⟨fun v ↦ by
    change binaryRelationInterpretationFormula.Evalb v ↔ v 0 = binaryRelationInterpretation (v 1) (v 2) (v 3)
    unfold binaryRelationInterpretation
    split <;> simp_all [binaryRelationInterpretationFormula, zero_def]⟩

instance binaryRelationInterpretationsFormula_defined :
    ℒₛₑₜ-function₂[V] (fun D E ↦ definableGraph (2 : V) (binaryRelationInterpretation D E) (by definability))
      via binaryRelationInterpretationsFormula :=
  ⟨fun v ↦ by
    change binaryRelationInterpretationsFormula.Evalb v ↔
      v 0 = definableGraph (2 : V) (binaryRelationInterpretation (v 1) (v 2)) (by definability)
    rw [mem_ext_iff]
    simp [binaryRelationInterpretationsFormula, mem_definableGraph_iff]⟩

instance binaryRelationStructureCodeFormula_defined :
    ℒₛₑₜ-function₂[V] binaryRelationStructureCode via binaryRelationStructureCodeFormula :=
  ⟨fun v ↦ by
    simp [binaryRelationStructureCodeFormula, binaryRelationStructureCode]
    constructor
    · intro h
      apply h
      intro r hr
      rw [hr]
    · intro h x hx
      exact h.trans (hx _ rfl).symm⟩

instance isCodedZFModelFormula_defined :
    ℒₛₑₜ-predicate[V] IsCodedZFModel via isCodedZFModelFormula :=
  ⟨fun v ↦ by simp [isCodedZFModelFormula, IsCodedZFModel]⟩

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ElementaryMap.codedZFModel_iff (j : ElementaryMap V W) (M : V) :
    IsCodedZFModel (j M) ↔ IsCodedZFModel M :=
  (j.map_defined isCodedZFModelFormula (fun v ↦ IsCodedZFModel (v 0))
    (fun v ↦ IsCodedZFModel (v 0)) ![M]).symm

end ZFVP
