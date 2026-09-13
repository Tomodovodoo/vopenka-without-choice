import ZFVP.Syntax.ZFVPOpenAxiomSet
import ZFVP.Syntax.UniformMembershipTemplates

/-! Shared parameter-free formulas for the full internal ZF and VP axiom sets. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def isMembershipFormulaCodeFormula : SetTheorySemisentence 2 :=
  f“n φ. !kpair.dfn n φ ∈ !formulaFamilyFormula (!membershipLanguageCodeFormula) (!isEmpty)”

def separationCodeFormula : SetTheorySemisentence 3 := separationTemplate.compileTailFormula

def replacementCodeFormula : SetTheorySemisentence 3 := replacementTemplate.compileTailFormula

def vopenkaCodeFormula : SetTheorySemisentence 2 := vopenkaTemplate.compileFormula

def fixedZFSentenceCodesFormula : SetTheorySemisentence 1 :=
  f“T. ∀ ψ, ψ ∈ T ↔
    ψ = !(encodeMembershipFormulaFormula Axiom.empty) ∨
    ψ = !(encodeMembershipFormulaFormula Axiom.extentionality) ∨
    ψ = !(encodeMembershipFormulaFormula Axiom.pairing) ∨
    ψ = !(encodeMembershipFormulaFormula Axiom.union) ∨
    ψ = !(encodeMembershipFormulaFormula Axiom.power) ∨
    ψ = !(encodeMembershipFormulaFormula Axiom.infinity) ∨
    ψ = !(encodeMembershipFormulaFormula Axiom.foundation) ∨
    ψ = !(encodeMembershipFormulaFormula equalityBasisSentence)”

def vopenkaAxiomCodesFormula : SetTheorySemisentence 1 :=
  f“T. ∀ ψ, ψ ∈ T ↔ ∃ φ, !isMembershipFormulaCodeFormula (!(numeralFormula 2)) φ ∧ ψ = !vopenkaCodeFormula φ”

def isZFOpenAxiomFormula : SetTheorySemisentence 2 :=
  f“n ψ. (n = !isEmpty ∧ ψ ∈ !fixedZFSentenceCodesFormula) ∨
    (n ∈ !isω ∧ ∃ φ, !isMembershipFormulaCodeFormula (!succ.dfn n) φ ∧ ψ = !separationCodeFormula n φ) ∨
    (n ∈ !isω ∧ ∃ φ, !isMembershipFormulaCodeFormula (!succ.dfn (!succ.dfn n)) φ ∧ ψ = !replacementCodeFormula n φ)”

def isZFVPOpenAxiomFormula : SetTheorySemisentence 2 :=
  f“n ψ. !isZFOpenAxiomFormula n ψ ∨ n = !isEmpty ∧ ψ ∈ !vopenkaAxiomCodesFormula”

def zfOpenAxiomCodesFormula : SetTheorySemisentence 1 :=
  f“T. ∀ p, p ∈ T ↔ p ∈ !formulaFamilyFormula (!membershipLanguageCodeFormula) (!isEmpty) ∧
    ∃ n ψ, p = !kpair.dfn n ψ ∧ !isZFOpenAxiomFormula n ψ”

def zfVPOpenAxiomCodesFormula : SetTheorySemisentence 1 :=
  f“T. ∀ p, p ∈ T ↔ p ∈ !formulaFamilyFormula (!membershipLanguageCodeFormula) (!isEmpty) ∧
    ∃ n ψ, p = !kpair.dfn n ψ ∧ !isZFVPOpenAxiomFormula n ψ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance isMembershipFormulaCodeFormula_defined :
    ℒₛₑₜ-relation[V] IsMembershipFormulaCode via isMembershipFormulaCodeFormula :=
  ⟨fun v ↦ by simp [isMembershipFormulaCodeFormula, IsMembershipFormulaCode]⟩

instance separationCodeFormula_defined : ℒₛₑₜ-function₂[V] separationCode via separationCodeFormula :=
  MembershipTemplate.compileTailFormula_defined separationTemplate

instance replacementCodeFormula_defined : ℒₛₑₜ-function₂[V] replacementCode via replacementCodeFormula :=
  MembershipTemplate.compileTailFormula_defined replacementTemplate

instance vopenkaCodeFormula_defined : ℒₛₑₜ-function₁[V] vopenkaCode via vopenkaCodeFormula :=
  MembershipTemplate.compileFormula_defined vopenkaTemplate

instance fixedZFSentenceCodesFormula_defined :
    ℒₛₑₜ-function₀[V] fixedZFSentenceCodes via fixedZFSentenceCodesFormula :=
  ⟨fun v ↦ by
    change fixedZFSentenceCodesFormula.Evalb v ↔ v 0 = (fixedZFSentenceCodes : V)
    rw [mem_ext_iff]
    simp [fixedZFSentenceCodesFormula, mem_fixedZFSentenceCodes_iff]⟩

instance vopenkaAxiomCodesFormula_defined :
    ℒₛₑₜ-function₀[V] vopenkaAxiomCodes via vopenkaAxiomCodesFormula :=
  ⟨fun v ↦ by
    change vopenkaAxiomCodesFormula.Evalb v ↔ v 0 = (vopenkaAxiomCodes : V)
    rw [mem_ext_iff]
    simp [vopenkaAxiomCodesFormula, mem_vopenkaAxiomCodes_iff]⟩

instance isZFOpenAxiomFormula_defined : ℒₛₑₜ-relation[V] IsZFOpenAxiom via isZFOpenAxiomFormula :=
  ⟨fun v ↦ by simp [isZFOpenAxiomFormula, IsZFOpenAxiom, zero_def]⟩

instance isZFVPOpenAxiomFormula_defined : ℒₛₑₜ-relation[V] IsZFVPOpenAxiom via isZFVPOpenAxiomFormula :=
  ⟨fun v ↦ by simp [isZFVPOpenAxiomFormula, IsZFVPOpenAxiom, zero_def]⟩

instance zfOpenAxiomCodesFormula_defined :
    ℒₛₑₜ-function₀[V] zfOpenAxiomCodes via zfOpenAxiomCodesFormula :=
  ⟨fun v ↦ by
    change zfOpenAxiomCodesFormula.Evalb v ↔ v 0 = (zfOpenAxiomCodes : V)
    rw [mem_ext_iff]
    simp [zfOpenAxiomCodesFormula, zfOpenAxiomCodes, mem_sep_iff]⟩

instance zfVPOpenAxiomCodesFormula_defined :
    ℒₛₑₜ-function₀[V] zfVPOpenAxiomCodes via zfVPOpenAxiomCodesFormula :=
  ⟨fun v ↦ by
    change zfVPOpenAxiomCodesFormula.Evalb v ↔ v 0 = (zfVPOpenAxiomCodes : V)
    rw [mem_ext_iff]
    simp [zfVPOpenAxiomCodesFormula, zfVPOpenAxiomCodes, mem_sep_iff]⟩

end ZFVP

