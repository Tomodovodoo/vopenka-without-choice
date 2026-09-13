import ZFVP.ModelTheory.UniformCodedSequents
import ZFVP.ModelTheory.OpenCodedSequentSoundness

/-! A shared first-order definition of the internally finite sequent proof checker. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def isCodedSequentRuleFormula : SetTheorySemisentence 4 :=
  f“T P n Γ.
  (n = !isEmpty ∧ ∃ φ ∈ T, Γ = !singleton.dfn φ) ∨
  (∃ φ ∈ !formulaSetFormula (!membershipLanguageCodeFormula) (!isEmpty) n,
    Γ = !SetTheory.insert.dfn φ (!singleton.dfn (!negateFormulaFormula (!membershipLanguageCodeFormula) (!isEmpty) n φ))) ∨
  Γ = !singleton.dfn (!truthCodeFormula) ∨
  (∃ Δ φ ψ, φ ∈ !formulaSetFormula (!membershipLanguageCodeFormula) (!isEmpty) n ∧
    ψ ∈ !formulaSetFormula (!membershipLanguageCodeFormula) (!isEmpty) n ∧
    Γ = !SetTheory.insert.dfn (!orCodeFormula φ ψ) Δ ∧
    !kpair.dfn n (!SetTheory.insert.dfn φ (!SetTheory.insert.dfn ψ Δ)) ∈ P) ∨
  (∃ Δ φ ψ, φ ∈ !formulaSetFormula (!membershipLanguageCodeFormula) (!isEmpty) n ∧
    ψ ∈ !formulaSetFormula (!membershipLanguageCodeFormula) (!isEmpty) n ∧
    Γ = !SetTheory.insert.dfn (!andCodeFormula φ ψ) Δ ∧
    !kpair.dfn n (!SetTheory.insert.dfn φ Δ) ∈ P ∧ !kpair.dfn n (!SetTheory.insert.dfn ψ Δ) ∈ P) ∨
  (∃ Δ Ξ φ, φ ∈ !formulaSetFormula (!membershipLanguageCodeFormula) (!isEmpty) n ∧
    Γ = !union.dfn Δ Ξ ∧ !kpair.dfn n (!SetTheory.insert.dfn φ Δ) ∈ P ∧
    !kpair.dfn n (!SetTheory.insert.dfn (!negateFormulaFormula (!membershipLanguageCodeFormula) (!isEmpty) n φ) Ξ) ∈ P) ∨
  (∃ Δ φ, (∀ ψ ∈ Δ, ψ ∈ !formulaSetFormula (!membershipLanguageCodeFormula) (!isEmpty) n) ∧
    φ ∈ !formulaSetFormula (!membershipLanguageCodeFormula) (!isEmpty) (!succ.dfn n) ∧
    Γ = !SetTheory.insert.dfn (!allCodeFormula φ) Δ ∧
    !kpair.dfn (!succ.dfn n) (!SetTheory.insert.dfn φ (!shiftCodedSequentFormula n Δ)) ∈ P) ∨
  (∃ Δ φ i, i ∈ n ∧ φ ∈ !formulaSetFormula (!membershipLanguageCodeFormula) (!isEmpty) (!succ.dfn n) ∧
    Γ = !SetTheory.insert.dfn (!existsCodeFormula φ) Δ ∧
    !kpair.dfn n (!SetTheory.insert.dfn (!instantiateMembershipFormulaFormula n i φ) Δ) ∈ P) ∨
  (∃ Δ, (∀ φ ∈ Δ, φ ∈ Γ) ∧ !kpair.dfn n Δ ∈ P) ∨
  ∃ m r Δ, m ∈ !isω ∧ r ∈ !function.dfn n m ∧
    (∀ φ ∈ Δ, φ ∈ !formulaSetFormula (!membershipLanguageCodeFormula) (!isEmpty) m) ∧
    Γ = !renameCodedSequentFormula m n r Δ ∧ !kpair.dfn m Δ ∈ P”

def isOpenCodedSequentRuleFormula : SetTheorySemisentence 4 :=
  f“T P n Γ. !isCodedSequentRuleFormula (!isEmpty) P n Γ ∨
    ∃ φ, !kpair.dfn n φ ∈ T ∧ Γ = !singleton.dfn φ”

def isOpenCodedSequentProofFormula : SetTheorySemisentence 4 :=
  f“T p n Γ. !IsFunction.dfn p ∧ ∃ l ∈ !isω, !domain.dfn p = !succ.dfn l ∧
    !value.dfn p l = !kpair.dfn n Γ ∧
    ∀ i ∈ !domain.dfn p, ∃ m Δ, !value.dfn p i = !kpair.dfn m Δ ∧ !isCodedSequentFormula m Δ ∧
      !isOpenCodedSequentRuleFormula T (!range.dfn (!restrict.dfn p i)) m Δ”

def noRefutationFormula (R : SetTheorySemisentence 4) : SetTheorySemisentence 1 :=
  f“T. ¬∃ p, !R T p (!isEmpty) (!isEmpty)”

def openCodedSequentConsistentFormula : SetTheorySemisentence 1 :=
  noRefutationFormula isOpenCodedSequentProofFormula

def codedZFVPConsistencySentence : SetTheorySentence :=
  f“!openCodedSequentConsistentFormula (!zfVPOpenAxiomCodesFormula)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance isCodedSequentRuleFormula_defined :
    ℒₛₑₜ-relation₄[V] IsCodedSequentRule via isCodedSequentRuleFormula :=
  ⟨fun v ↦ by simp [isCodedSequentRuleFormula, IsCodedSequentRule, zero_def, subset_def]⟩

instance isOpenCodedSequentRuleFormula_defined :
    ℒₛₑₜ-relation₄[V] IsOpenCodedSequentRule via isOpenCodedSequentRuleFormula :=
  ⟨fun v ↦ by simp [isOpenCodedSequentRuleFormula, IsOpenCodedSequentRule]⟩

instance isOpenCodedSequentProofFormula_defined :
    ℒₛₑₜ-relation₄[V] IsOpenCodedSequentProof via isOpenCodedSequentProofFormula :=
  ⟨fun v ↦ by simp [isOpenCodedSequentProofFormula, IsOpenCodedSequentProof]⟩

instance noRefutationFormula_defined (P : V → V → V → V → Prop) (R : SetTheorySemisentence 4)
    [ℒₛₑₜ-relation₄[V] P via R] :
    ℒₛₑₜ-predicate[V] (fun T ↦ ¬∃ p, P T p 0 ∅) via noRefutationFormula R :=
  ⟨fun v ↦ by simp [noRefutationFormula, zero_def]⟩

instance openCodedSequentConsistentFormula_defined :
    ℒₛₑₜ-predicate[V] OpenCodedSequentConsistent via openCodedSequentConsistentFormula :=
  noRefutationFormula_defined IsOpenCodedSequentProof isOpenCodedSequentProofFormula

@[simp] theorem eval_codedZFVPConsistencySentence :
    codedZFVPConsistencySentence.Evalb (![] : Fin 0 → V) ↔
      OpenCodedSequentConsistent (zfVPOpenAxiomCodes : V) := by
  simp [codedZFVPConsistencySentence]

end ZFVP
