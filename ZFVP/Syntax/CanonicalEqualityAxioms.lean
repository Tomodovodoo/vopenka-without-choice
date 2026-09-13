import ZFVP.Syntax.BinaryRelationInternalSemantics
import ZFVP.Syntax.UniformZFVPAxioms
import ZFVP.SetTheory.FiniteSets

/-! A finite equality basis for the raw internal membership syntax, together
with a nonempty-domain axiom. Open axioms are universally interpreted. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def nonemptyDomainSentence : SetTheorySentence := ∃¹ (⊤ : SetTheorySemisentence 1)

def boundPairArgumentsFormula : SetTheorySemisentence 3 :=
  f“a i j. a = !assignmentPrependFormula (!(numeralFormula 1))
    (!assignmentPrependFormula (!isEmpty) (!isEmpty) (!boundVarCodeFormula j)) (!boundVarCodeFormula i)”

def rawEqualityBridgeCodeFormula : SetTheorySemisentence 1 :=
  f“φ. ∃ a, a = !boundPairArgumentsFormula (!isEmpty) (!(numeralFormula 1)) ∧
    φ = !andCodeFormula
      (!orCodeFormula (!negAtomCodeFormula (!isEmpty) a) (!atomCodeFormula (!relationTokenFormula (!isEmpty)) a))
      (!orCodeFormula (!negAtomCodeFormula (!relationTokenFormula (!isEmpty)) a) (!atomCodeFormula (!isEmpty) a))”

def canonicalEqualityOpenCodesFormula : SetTheorySemisentence 1 :=
  f“T. T = !SetTheory.insert.dfn
    (!kpair.dfn (!isEmpty) (!(encodeMembershipFormulaFormula equalityBasisSentence)))
    (!doubleton.dfn (!kpair.dfn (!(numeralFormula 2)) (!rawEqualityBridgeCodeFormula))
      (!kpair.dfn (!isEmpty) (!(encodeMembershipFormulaFormula nonemptyDomainSentence))))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def rawEqualityBridgeCode : V :=
  andCode
    (orCode (negAtomCode equalityToken (boundPairArguments 0 1))
      (atomCode (relationToken 0) (boundPairArguments 0 1)))
    (orCode (negAtomCode (relationToken 0) (boundPairArguments 0 1))
      (atomCode equalityToken (boundPairArguments 0 1)))

noncomputable def canonicalEqualityOpenCodes : V :=
  {⟨0, encodeMembershipFormula equalityBasisSentence⟩ₖ, ⟨2, rawEqualityBridgeCode⟩ₖ,
    ⟨0, encodeMembershipFormula nonemptyDomainSentence⟩ₖ}

instance boundPairArgumentsFormula_defined :
    ℒₛₑₜ-function₂[V] boundPairArguments via boundPairArgumentsFormula :=
  ⟨fun v ↦ by simp [boundPairArgumentsFormula, boundPairArguments, standardTuple, zero_def]⟩

instance rawEqualityBridgeCodeFormula_defined :
    ℒₛₑₜ-function₀[V] rawEqualityBridgeCode via rawEqualityBridgeCodeFormula :=
  ⟨fun v ↦ by simp [rawEqualityBridgeCodeFormula, rawEqualityBridgeCode, equalityToken, zero_def]⟩

instance canonicalEqualityOpenCodesFormula_defined :
    ℒₛₑₜ-function₀[V] canonicalEqualityOpenCodes via canonicalEqualityOpenCodesFormula :=
  ⟨fun v ↦ by simp [canonicalEqualityOpenCodesFormula, canonicalEqualityOpenCodes, zero_def, pair_eq_doubleton]⟩

instance rawEqualityBridgeCode_definable : Language.DefinableFunction₀ ℒₛₑₜ (rawEqualityBridgeCode : V) :=
  rawEqualityBridgeCodeFormula_defined.to_definable

instance canonicalEqualityOpenCodes_definable : Language.DefinableFunction₀ ℒₛₑₜ (canonicalEqualityOpenCodes : V) :=
  canonicalEqualityOpenCodesFormula_defined.to_definable

private theorem bridge_atomic (r : V) (hr : r = equalityToken ∨ r = relationToken (0 : V)) :
    IsAtomicArguments membershipLanguageCode ∅ (2 : V) r (boundPairArguments 0 1) := by
  apply (membershipAtomicArguments_iff (by simp)).mpr
  exact ⟨hr.imp_right Or.inl, 0, by simp, 1, by simp, rfl⟩

theorem rawEqualityBridgeCode_valid :
    rawEqualityBridgeCode ∈ formulaSet membershipLanguageCode ∅ (2 : V) := by
  have hL := formulaSet_atoms membershipLanguageCode_valid (by simp)
    (bridge_atomic (equalityToken : V) (Or.inl rfl))
  have hR := formulaSet_atoms membershipLanguageCode_valid (by simp)
    (bridge_atomic (relationToken (0 : V)) (Or.inr rfl))
  exact (formulaSet_binary membershipLanguageCode_valid (by simp)
    (formulaSet_binary membershipLanguageCode_valid (by simp) hL.2 hR.1).2
    (formulaSet_binary membershipLanguageCode_valid (by simp) hR.2 hL.1).2).1

theorem canonicalEqualityOpenCodes_valid :
    (canonicalEqualityOpenCodes : V) ⊆ formulaFamily membershipLanguageCode ∅ := by
  intro p hp
  rcases (show p = ⟨0, encodeMembershipFormula equalityBasisSentence⟩ₖ ∨
      p = ⟨2, rawEqualityBridgeCode⟩ₖ ∨ p = ⟨0, encodeMembershipFormula nonemptyDomainSentence⟩ₖ
      from by simpa [canonicalEqualityOpenCodes] using hp) with rfl | rfl | rfl
  · exact encodeSentence_valid equalityBasisSentence
  · exact (mem_formulaSet_iff _ _ _ _).mp rawEqualityBridgeCode_valid
  · exact encodeSentence_valid nonemptyDomainSentence

theorem canonicalEqualityOpenCodes_finite : IsInternallyFinite (canonicalEqualityOpenCodes : V) := by
  have he : (canonicalEqualityOpenCodes : V) = insert ⟨0, encodeMembershipFormula equalityBasisSentence⟩ₖ
      (insert ⟨2, rawEqualityBridgeCode⟩ₖ (insert ⟨0, encodeMembershipFormula nonemptyDomainSentence⟩ₖ (∅ : V))) := by
    ext x
    simp [canonicalEqualityOpenCodes]
  rw [he]
  exact internallyFinite_insert (internallyFinite_insert
    (internallyFinite_insert (internallyFinite_empty (V := V)) _) _) _

theorem rawEqualityBridgeCode_satisfies {D E b : V} (hb : b ∈ D ^ (2 : V)) :
    Satisfies membershipLanguageCode ∅ (binaryRelationStructureCode D E) ∅ 2 rawEqualityBridgeCode b := by
  have haL := bridge_atomic (equalityToken : V) (Or.inl rfl)
  have haR := bridge_atomic (relationToken (0 : V)) (Or.inr rfl)
  have hL := formulaSet_atoms membershipLanguageCode_valid (by simp) haL
  have hR := formulaSet_atoms membershipLanguageCode_valid (by simp) haR
  have hb' : b ∈ structureDomain (binaryRelationStructureCode D E) ^ (2 : V) := by
    simpa only [binaryRelationStructureCode_domain] using hb
  rw [rawEqualityBridgeCode, satisfies_and membershipLanguageCode_valid (by simp)
    (formulaSet_binary membershipLanguageCode_valid (by simp) hL.2 hR.1).2
    (formulaSet_binary membershipLanguageCode_valid (by simp) hR.2 hL.1).2 hb',
    satisfies_or membershipLanguageCode_valid (by simp) hL.2 hR.1 hb',
    satisfies_or membershipLanguageCode_valid (by simp) hR.2 hL.1 hb',
    satisfies_negAtom membershipLanguageCode_valid (by simp) haL hb',
    satisfies_negAtom membershipLanguageCode_valid (by simp) haR hb',
    satisfies_atom membershipLanguageCode_valid (by simp) haL hb',
    satisfies_atom membershipLanguageCode_valid (by simp) haR hb',
    binaryAtomic_logicalEquality (by simp) (by simp) (by simp),
    binaryAtomic_relationEquality (by simp) (by simp) (by simp) hb]
  tauto

end ZFVP
