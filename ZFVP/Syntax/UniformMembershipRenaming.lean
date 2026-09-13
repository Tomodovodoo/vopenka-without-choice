import ZFVP.Syntax.UniformFormulaSubstitution
import ZFVP.Syntax.MembershipRenaming
import ZFVP.SetTheory.UniformLowTruth

/-! A parameter-free dictionary for internal membership-variable renaming. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundVariableAssignmentFormula : SetTheorySemisentence 2 :=
  f“B m. ∀ p, p ∈ B ↔ ∃ i ∈ m, p = !kpair.dfn i (!boundVarCodeFormula i)”

def renameMembershipFormulaFormula : SetTheorySemisentence 5 :=
  f“ψ n m r φ. ψ = !substituteFormulaFormula (!membershipLanguageCodeFormula) (!isEmpty) (!isEmpty)
    (!substitutionStateFormula n m (!composeFormula r (!boundVariableAssignmentFormula m)) (!isEmpty)) φ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundVariableAssignmentFormula_defined :
    ℒₛₑₜ-function₁[V] boundVariableAssignment via boundVariableAssignmentFormula :=
  ⟨fun v ↦ by
    change boundVariableAssignmentFormula.Evalb v ↔ v 0 = boundVariableAssignment (v 1)
    rw [mem_ext_iff]
    simp [boundVariableAssignmentFormula, boundVariableAssignment, mem_definableGraph_iff]⟩

instance renameMembershipFormulaFormula_defined :
    ℒₛₑₜ-function₄[V] renameMembershipFormula via renameMembershipFormulaFormula :=
  ⟨fun v ↦ by simp [renameMembershipFormulaFormula, renameMembershipFormula]⟩

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_substituteFormula (j : ElementaryMap V W) (L Γ Δ s φ : V) :
    j (substituteFormula L Γ Δ s φ) = substituteFormula (j L) (j Γ) (j Δ) (j s) (j φ) :=
  j.map_definedFunction substituteFormulaFormula
    (fun v ↦ substituteFormula (v 0) (v 1) (v 2) (v 3) (v 4))
    (fun v ↦ substituteFormula (v 0) (v 1) (v 2) (v 3) (v 4)) ![L, Γ, Δ, s, φ]

theorem map_renameMembershipFormula (j : ElementaryMap V W) (n m r φ : V) :
    j (renameMembershipFormula n m r φ) = renameMembershipFormula (j n) (j m) (j r) (j φ) :=
  j.map_definedFunction renameMembershipFormulaFormula
    (fun v ↦ renameMembershipFormula (v 0) (v 1) (v 2) (v 3))
    (fun v ↦ renameMembershipFormula (v 0) (v 1) (v 2) (v 3)) ![n, m, r, φ]

end ElementaryMap

end ZFVP
