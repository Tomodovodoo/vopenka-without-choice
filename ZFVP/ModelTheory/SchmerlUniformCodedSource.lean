import ZFVP.ModelTheory.SchmerlCodedRubinSource
import ZFVP.ModelTheory.UniformBinaryRelationStructure
import ZFVP.SetTheory.ForcingDictionary

/-! Fixed first-order definitions of the internal Rubin source predicates.
No ambient-model-dependent definability choice is used for transfer. -/
namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def codedSatisfiesFormula : SetTheorySemisentence 4 :=
  f“M n φ b. !satisfiesFormula (!membershipLanguageCodeFormula) (!isEmpty) M (!isEmpty) n φ b”

def codedUnaryFormula : SetTheorySemisentence 3 :=
  f“M φ x. !codedSatisfiesFormula M (!(numeralFormula 1)) φ
    (!assignmentPrependFormula (!isEmpty) (!isEmpty) x)”

def codedBinaryFormula : SetTheorySemisentence 4 :=
  f“M φ x y. !codedSatisfiesFormula M (!(numeralFormula 2)) φ
    (!assignmentPrependFormula (!(numeralFormula 1))
      (!assignmentPrependFormula (!isEmpty) (!isEmpty) y) x)”

def codedMemberFormula : SetTheorySemisentence 3 :=
  f“M x a. !codedBinaryFormula M (!(encodeMembershipFormulaFormula (“x a. x ∈ a” : SetTheorySemisentence 2))) x a”

def codedMemberTraceFormula : SetTheorySemisentence 3 :=
  f“T M a. ∀ x, x ∈ T ↔ x ∈ !structureDomainFormula M ∧ !codedMemberFormula M x a”

def isCodedFinSmallFormula : SetTheorySemisentence 1 :=
  f“M. ∀ a ∈ !structureDomainFormula M,
    !codedUnaryFormula M (!(encodeMembershipFormulaFormula internallyFiniteFormula)) a →
      !internallyCountableFormula (!codedMemberTraceFormula M a)”

def isCodedDefinableSetFormula : SetTheorySemisentence 2 :=
  f“M A. A ⊆ !structureDomainFormula M ∧
    ∃ n ∈ !isω, ∃ φ ∈ !formulaSetFormula (!membershipLanguageCodeFormula) (!isEmpty) (!succ.dfn n),
      ∃ b ∈ !function.dfn (!structureDomainFormula M) n, ∀ x ∈ !structureDomainFormula M,
        x ∈ A ↔ !codedSatisfiesFormula M (!succ.dfn n) φ (!assignmentPrependFormula n b x)”

def isCodedDefinableRelationFormula : SetTheorySemisentence 2 :=
  f“M R. R ⊆ !prod.dfn (!structureDomainFormula M) (!structureDomainFormula M) ∧
    ∃ n ∈ !isω, ∃ φ ∈ !formulaSetFormula (!membershipLanguageCodeFormula) (!isEmpty) (!succ.dfn (!succ.dfn n)),
      ∃ b ∈ !function.dfn (!structureDomainFormula M) n,
        ∀ x ∈ !structureDomainFormula M, ∀ y ∈ !structureDomainFormula M,
          !kpair.dfn x y ∈ R ↔ !codedSatisfiesFormula M (!succ.dfn (!succ.dfn n)) φ
            (!assignmentPrependFormula (!succ.dfn n) (!assignmentPrependFormula n b y) x)”

def isInternalDirectedNoMaxFormula : SetTheorySemisentence 2 :=
  f“P R. !isNonempty P ∧
    (∀ x ∈ P, ∀ y ∈ P, ∃ z ∈ P, !kpair.dfn x z ∈ R ∧ !kpair.dfn y z ∈ R) ∧
    ¬∃ m ∈ P, ∀ x ∈ P, !kpair.dfn x m ∈ R”

def isInternalCofinalStrictChainFormula : SetTheorySemisentence 4 :=
  f“κ P R c. c ∈ !function.dfn P κ ∧
    (∀ i ∈ κ, ∀ j ∈ κ, i ∈ j →
      !kpair.dfn (!value.dfn c i) (!value.dfn c j) ∈ R ∧ !value.dfn c i ≠ !value.dfn c j) ∧
    ∀ x ∈ P, ∃ i ∈ κ, !kpair.dfn x (!value.dfn c i) ∈ R”

def isInternalMaximallyCompatibleFormula : SetTheorySemisentence 3 :=
  f“P R F. F ⊆ P ∧
    (∀ x ∈ F, ∀ y ∈ F, ∃ z ∈ F, !kpair.dfn x z ∈ R ∧ !kpair.dfn y z ∈ R) ∧
    ∀ q ∈ P, (∀ p ∈ F, ∃ z ∈ P, !kpair.dfn p z ∈ R ∧ !kpair.dfn q z ∈ R) → q ∈ F”

def isCodedRubinFormula : SetTheorySemisentence 2 :=
  f“M κ. (∀ P R, !isCodedDefinableSetFormula M P → !isCodedDefinableRelationFormula M R →
    !forcingPosetFormula P R → !isInternalDirectedNoMaxFormula P R →
      ∃ c, !isInternalCofinalStrictChainFormula κ P R c) ∧
    (∀ P R, !isCodedDefinableSetFormula M P → !isCodedDefinableRelationFormula M R →
      !forcingPosetFormula P R → ∀ F, !isInternalMaximallyCompatibleFormula P R F →
        (∃ c, !isInternalCofinalStrictChainFormula κ F R c) → !isCodedDefinableSetFormula M F)”

def isCodedRubinFinSmallSourceFormula : SetTheorySemisentence 1 :=
  f“M. (∃ D E, M = !binaryRelationStructureCodeFormula D E ∧ E ⊆ !prod.dfn D D) ∧
    !isCodedZFModelFormula M ∧ !CardLE.dfn (!structureDomainFormula M) (!hartogsNumberFormula (!isω)) ∧
    !isCodedRubinFormula M (!hartogsNumberFormula (!isω)) ∧ !isCodedFinSmallFormula M”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance codedSatisfiesFormula_defined : ℒₛₑₜ-relation₄[V] codedSatisfies via codedSatisfiesFormula :=
  ⟨fun v ↦ by simp [codedSatisfiesFormula, codedSatisfies]⟩
instance codedUnaryFormula_defined : ℒₛₑₜ-relation₃[V] codedUnary via codedUnaryFormula :=
  ⟨fun v ↦ by simp [codedUnaryFormula, codedUnary, standardTuple, zero_def]⟩
instance codedBinaryFormula_defined : ℒₛₑₜ-relation₄[V] codedBinary via codedBinaryFormula :=
  ⟨fun v ↦ by simp [codedBinaryFormula, codedBinary, standardTuple, zero_def]⟩
instance codedMemberFormula_defined : ℒₛₑₜ-relation₃[V] codedMember via codedMemberFormula :=
  ⟨fun v ↦ by simp [codedMemberFormula, codedMember]⟩
instance codedMemberTraceFormula_defined : ℒₛₑₜ-function₂[V] codedMemberTrace via codedMemberTraceFormula :=
  ⟨fun v ↦ by
    change codedMemberTraceFormula.Evalb v ↔ v 0 = codedMemberTrace (v 1) (v 2)
    rw [mem_ext_iff]
    simp [codedMemberTraceFormula, codedMemberTrace]⟩
instance isCodedFinSmallFormula_defined : ℒₛₑₜ-predicate[V] IsCodedFinSmall via isCodedFinSmallFormula :=
  ⟨fun v ↦ by simp [isCodedFinSmallFormula, IsCodedFinSmall]⟩
instance isCodedDefinableSetFormula_defined : ℒₛₑₜ-relation[V] IsCodedDefinableSet via isCodedDefinableSetFormula :=
  ⟨fun v ↦ by simp [isCodedDefinableSetFormula, IsCodedDefinableSet]⟩
instance isCodedDefinableRelationFormula_defined :
    ℒₛₑₜ-relation[V] IsCodedDefinableRelation via isCodedDefinableRelationFormula :=
  ⟨fun v ↦ by simp [isCodedDefinableRelationFormula, IsCodedDefinableRelation]⟩
instance isInternalDirectedNoMaxFormula_defined :
    ℒₛₑₜ-relation[V] IsInternalDirectedNoMax via isInternalDirectedNoMaxFormula :=
  ⟨fun v ↦ by simp [isInternalDirectedNoMaxFormula, IsInternalDirectedNoMax]⟩
instance isInternalCofinalStrictChainFormula_defined :
    ℒₛₑₜ-relation₄[V] IsInternalCofinalStrictChain via isInternalCofinalStrictChainFormula :=
  ⟨fun v ↦ by simp [isInternalCofinalStrictChainFormula, IsInternalCofinalStrictChain]⟩
instance isInternalMaximallyCompatibleFormula_defined :
    ℒₛₑₜ-relation₃[V] IsInternalMaximallyCompatible via isInternalMaximallyCompatibleFormula :=
  ⟨fun v ↦ by simp [isInternalMaximallyCompatibleFormula, IsInternalMaximallyCompatible]⟩
instance isCodedRubinFormula_defined : ℒₛₑₜ-relation[V] IsCodedRubin via isCodedRubinFormula :=
  ⟨fun v ↦ by simp [isCodedRubinFormula, IsCodedRubin]⟩
instance isCodedRubinFinSmallSourceFormula_defined :
    ℒₛₑₜ-predicate[V] IsCodedRubinFinSmallSource via isCodedRubinFinSmallSourceFormula :=
  ⟨fun v ↦ by simp [isCodedRubinFinSmallSourceFormula, IsCodedRubinFinSmallSource]⟩

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ElementaryMap.codedRubinFinSmallSource_iff (j : ZFVP.ElementaryMap V W) (M : V) :
    IsCodedRubinFinSmallSource (j M) ↔ IsCodedRubinFinSmallSource M :=
  (j.map_defined isCodedRubinFinSmallSourceFormula (fun v ↦ IsCodedRubinFinSmallSource (v 0))
    (fun v ↦ IsCodedRubinFinSmallSource (v 0)) ![M]).symm

end ZFVP.Schmerl
