import ZFVP.Syntax.BoundedCodes
import ZFVP.SetTheory.UniformLowTruth

/-! Shared first-order definitions of the internal bounded-formula family. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedGuardArgumentsFormula : SetTheorySemisentence 2 :=
  f“args i. args = !assignmentPrependFormula (!(numeralFormula 1))
    (!assignmentPrependFormula (!isEmpty) (!isEmpty) (!boundVarCodeFormula (!succ.dfn i)))
    (!boundVarCodeFormula (!isEmpty))”

def boundedAllCodeFormula : SetTheorySemisentence 3 :=
  f“c i φ. c = !allCodeFormula (!orCodeFormula
    (!negAtomCodeFormula (!relationTokenFormula (!(numeralFormula 1))) (!boundedGuardArgumentsFormula i)) φ)”

def boundedExistsCodeFormula : SetTheorySemisentence 3 :=
  f“c i φ. c = !existsCodeFormula (!andCodeFormula
    (!atomCodeFormula (!relationTokenFormula (!(numeralFormula 1))) (!boundedGuardArgumentsFormula i)) φ)”

def isBoundedFormulaClosedFormula : SetTheorySemisentence 1 :=
  f“Q. ∀ n ∈ !isω,
    (!kpair.dfn n (!truthCodeFormula) ∈ Q ∧ !kpair.dfn n (!falsityCodeFormula) ∈ Q) ∧
    (∀ r args, !isAtomicArgumentsFormula (!membershipLanguageCodeFormula) (!isEmpty) n r args →
      !kpair.dfn n (!atomCodeFormula r args) ∈ Q ∧ !kpair.dfn n (!negAtomCodeFormula r args) ∈ Q) ∧
    (∀ φ ψ, !kpair.dfn n φ ∈ Q → !kpair.dfn n ψ ∈ Q →
      !kpair.dfn n (!andCodeFormula φ ψ) ∈ Q ∧ !kpair.dfn n (!orCodeFormula φ ψ) ∈ Q) ∧
    ∀ i ∈ n, ∀ φ, !kpair.dfn (!succ.dfn n) φ ∈ Q →
      !kpair.dfn n (!boundedAllCodeFormula i φ) ∈ Q ∧ !kpair.dfn n (!boundedExistsCodeFormula i φ) ∈ Q”

def boundedFormulaFamilyFormula : SetTheorySemisentence 1 :=
  f“F. ∀ p, p ∈ F ↔ p ∈ !formulaFamilyFormula (!membershipLanguageCodeFormula) (!isEmpty) ∧
    ∀ Q, !isBoundedFormulaClosedFormula Q → p ∈ Q”

def isBoundedFormulaCodeFormula : SetTheorySemisentence 2 :=
  f“n φ. !kpair.dfn n φ ∈ !boundedFormulaFamilyFormula”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedGuardArgumentsFormula_defined :
    ℒₛₑₜ-function₁[V] boundedGuardArguments via boundedGuardArgumentsFormula :=
  ⟨fun v ↦ by simp [boundedGuardArgumentsFormula, boundedGuardArguments, standardTuple, zero_def]⟩

instance boundedAllCodeFormula_defined : ℒₛₑₜ-function₂[V] boundedAllCode via boundedAllCodeFormula :=
  ⟨fun v ↦ by simp [boundedAllCodeFormula, boundedAllCode]⟩

instance boundedExistsCodeFormula_defined : ℒₛₑₜ-function₂[V] boundedExistsCode via boundedExistsCodeFormula :=
  ⟨fun v ↦ by simp [boundedExistsCodeFormula, boundedExistsCode]⟩

instance isBoundedFormulaClosedFormula_defined :
    ℒₛₑₜ-predicate[V] IsBoundedFormulaClosed via isBoundedFormulaClosedFormula :=
  ⟨fun v ↦ by simp [isBoundedFormulaClosedFormula, IsBoundedFormulaClosed]⟩

instance boundedFormulaFamilyFormula_defined :
    ℒₛₑₜ-function₀[V] boundedFormulaFamily via boundedFormulaFamilyFormula := ⟨fun v ↦ by
  change boundedFormulaFamilyFormula.Evalb v ↔ v 0 = boundedFormulaFamily
  rw [mem_ext_iff]
  simp [boundedFormulaFamilyFormula, mem_boundedFormulaFamily_iff]⟩

instance isBoundedFormulaCodeFormula_defined :
    ℒₛₑₜ-relation[V] IsBoundedFormulaCode via isBoundedFormulaCodeFormula :=
  ⟨fun v ↦ by simp [isBoundedFormulaCodeFormula, IsBoundedFormulaCode]⟩

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_boundedFormulaCode_iff (j : ElementaryMap V W) (n φ : V) :
    IsBoundedFormulaCode (j n) (j φ) ↔ IsBoundedFormulaCode n φ :=
  (j.map_defined isBoundedFormulaCodeFormula (fun v ↦ IsBoundedFormulaCode (v 0) (v 1))
    (fun v ↦ IsBoundedFormulaCode (v 0) (v 1)) ![n, φ]).symm

end ElementaryMap
end ZFVP
