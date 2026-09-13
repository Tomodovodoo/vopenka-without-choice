import ZFVP.ModelTheory.CodedSequentQuantifiers
import ZFVP.Syntax.UniformZFVPAxioms

/-! Parameter-free definitions of internal sequents and their variable operations. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def isCodedSequentFormula : SetTheorySemisentence 2 :=
  f“n Γ. n ∈ !isω ∧ !internallyFiniteFormula Γ ∧
    ∀ φ ∈ Γ, φ ∈ !formulaSetFormula (!membershipLanguageCodeFormula) (!isEmpty) n”

def successorIndicesFormula : SetTheorySemisentence 2 :=
  f“R n. ∀ p, p ∈ R ↔ ∃ i ∈ n, p = !kpair.dfn i (!succ.dfn i)”

def renameCodedSequentFormula : SetTheorySemisentence 5 :=
  f“R n m r Γ. ∀ ψ, ψ ∈ R ↔ ∃ φ ∈ Γ, ψ = !renameMembershipFormulaFormula n m r φ”

def shiftCodedSequentFormula : SetTheorySemisentence 3 :=
  f“R n Γ. R = !renameCodedSequentFormula n (!succ.dfn n) (!successorIndicesFormula n) Γ”

def instantiateMembershipFormulaFormula : SetTheorySemisentence 4 :=
  f“ψ n i φ. ψ = !renameMembershipFormulaFormula (!succ.dfn n) n
    (!assignmentPrependFormula n (!identity.dfn n) i) φ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance isCodedSequentFormula_defined : ℒₛₑₜ-relation[V] IsCodedSequent via isCodedSequentFormula :=
  ⟨fun v ↦ by simp [isCodedSequentFormula, IsCodedSequent, subset_def]⟩

instance successorIndicesFormula_defined : ℒₛₑₜ-function₁[V] successorIndices via successorIndicesFormula :=
  ⟨fun v ↦ by
    change successorIndicesFormula.Evalb v ↔ v 0 = successorIndices (v 1)
    rw [mem_ext_iff]
    simp [successorIndicesFormula, successorIndices, mem_definableGraph_iff]⟩

instance renameCodedSequentFormula_defined :
    ℒₛₑₜ-function₄[V] renameCodedSequent via renameCodedSequentFormula :=
  ⟨fun v ↦ by
    change renameCodedSequentFormula.Evalb v ↔ v 0 = renameCodedSequent (v 1) (v 2) (v 3) (v 4)
    rw [mem_ext_iff]
    simp [renameCodedSequentFormula, mem_renameCodedSequent_iff]⟩

instance shiftCodedSequentFormula_defined :
    ℒₛₑₜ-function₂[V] shiftCodedSequent via shiftCodedSequentFormula :=
  ⟨fun v ↦ by simp [shiftCodedSequentFormula, shiftCodedSequent]⟩

instance instantiateMembershipFormulaFormula_defined :
    ℒₛₑₜ-function₃[V] instantiateMembershipFormula via instantiateMembershipFormulaFormula :=
  ⟨fun v ↦ by simp [instantiateMembershipFormulaFormula, instantiateMembershipFormula]⟩

end ZFVP

