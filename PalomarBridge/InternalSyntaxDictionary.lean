import PalomarBridge.CodingOperations
import ZFVP.Syntax.Formulas
import ZFVP.ModelTheory.StructureCode

namespace PalomarBridge
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {M : Type u} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "mem" => (fun x y : M => x ∈ y)

@[simp] theorem coding_language (F R fa ra : M) :
    Coding.language mem F R fa ra = ZFVP.languageCode F R fa ra := by
  simp [Coding.language, ZFVP.languageCode]
@[simp] theorem coding_functionSymbols (L : M) :
    Coding.functionSymbols mem L = ZFVP.functionSymbols L := by
  simp [Coding.functionSymbols, ZFVP.functionSymbols]
@[simp] theorem coding_relationSymbols (L : M) :
    Coding.relationSymbols mem L = ZFVP.relationSymbols L := by
  simp [Coding.relationSymbols, ZFVP.relationSymbols]
@[simp] theorem coding_functionArities (L : M) :
    Coding.functionArities mem L = ZFVP.functionArities L := by
  simp [Coding.functionArities, ZFVP.functionArities]
@[simp] theorem coding_relationArities (L : M) :
    Coding.relationArities mem L = ZFVP.relationArities L := by
  simp [Coding.relationArities, ZFVP.relationArities]
@[simp] theorem coding_isLanguage (L : M) :
    Coding.IsLanguage mem L ↔ ZFVP.IsLanguageCode L := by
  simp [Coding.IsLanguage, ZFVP.IsLanguageCode]
@[simp] theorem coding_structureCode (A FI RI : M) :
    Coding.structureCode mem A FI RI = ZFVP.structureCode A FI RI := by
  simp [Coding.structureCode, ZFVP.structureCode]
@[simp] theorem coding_structureDomain (S : M) :
    Coding.structureDomain mem S = ZFVP.structureDomain S := by
  simp [Coding.structureDomain, ZFVP.structureDomain]
@[simp] theorem coding_structureFunctions (S : M) :
    Coding.structureFunctions mem S = ZFVP.structureFunctions S := by
  simp [Coding.structureFunctions, ZFVP.structureFunctions]
@[simp] theorem coding_structureRelations (S : M) :
    Coding.structureRelations mem S = ZFVP.structureRelations S := by
  simp [Coding.structureRelations, ZFVP.structureRelations]
@[simp] theorem coding_isStructure (L S : M) :
    Coding.IsStructure mem L S ↔ ZFVP.IsStructureCode L S := by
  simp [Coding.IsStructure, ZFVP.IsStructureCode, isNonempty_def, subset_def]
@[simp] theorem coding_boundVar (i : M) : Coding.boundVar mem i = ZFVP.boundVarCode i := by
  simp [Coding.boundVar, ZFVP.boundVarCode]
@[simp] theorem coding_functionTerm (f args : M) :
    Coding.functionTerm mem f args = ZFVP.functionTermCode f args := by
  simp [Coding.functionTerm, ZFVP.functionTermCode]
@[simp] theorem coding_termClosed (L n T : M) :
    Coding.TermClosed mem L n T ↔ ZFVP.IsTermClosed L ∅ n T := by
  simp [Coding.TermClosed, ZFVP.IsTermClosed]

@[simp] theorem coding_terms {L n : M} (hL : ZFVP.IsLanguageCode L) (hn : n ∈ (ω : M)) :
    Coding.terms mem L n = ZFVP.termSet L ∅ n := by
  apply setValue_eq
  intro t
  simp only [ZFVP.mem_termSet_iff, coding_termClosed]
  constructor
  · exact And.right
  · intro h
    exact ⟨h _ (ZFVP.syntaxUniverse_termClosed hL hn ∅), h⟩

@[simp] theorem coding_truthCode : Coding.truthCode mem = (ZFVP.truthCode : M) := by
  simp [Coding.truthCode, ZFVP.truthCode]
@[simp] theorem coding_falsityCode : Coding.falsityCode mem = (ZFVP.falsityCode : M) := by
  simp [Coding.falsityCode, ZFVP.falsityCode]
@[simp] theorem coding_atom (r a : M) : Coding.atom mem r a = ZFVP.atomCode r a := by
  simp [Coding.atom, ZFVP.atomCode]
@[simp] theorem coding_negAtom (r a : M) : Coding.negAtom mem r a = ZFVP.negAtomCode r a := by
  simp [Coding.negAtom, ZFVP.negAtomCode]
@[simp] theorem coding_conjunction (p q : M) : Coding.conjunction mem p q = ZFVP.andCode p q := by
  simp [Coding.conjunction, ZFVP.andCode]
@[simp] theorem coding_disjunction (p q : M) : Coding.disjunction mem p q = ZFVP.orCode p q := by
  simp [Coding.disjunction, ZFVP.orCode]
@[simp] theorem coding_universal (p : M) : Coding.universal mem p = ZFVP.allCode p := by
  simp [Coding.universal, ZFVP.allCode]
@[simp] theorem coding_existential (p : M) : Coding.existential mem p = ZFVP.existsCode p := by
  simp [Coding.existential, ZFVP.existsCode]

@[simp] theorem coding_atomicArguments {L n : M} (hL : ZFVP.IsLanguageCode L)
    (hn : n ∈ (ω : M)) (r args : M) :
    Coding.AtomicArguments mem L n r args ↔ ZFVP.IsAtomicArguments L ∅ n r args := by
  simp [Coding.AtomicArguments, ZFVP.IsAtomicArguments, coding_terms hL hn,
    ZFVP.equalityToken, ZFVP.relationToken]

@[simp] theorem coding_formulaClosed {L : M} (hL : ZFVP.IsLanguageCode L) (Q : M) :
    Coding.FormulaClosed mem L Q ↔ ZFVP.IsFormulaClosed L ∅ Q := by
  unfold Coding.FormulaClosed ZFVP.IsFormulaClosed
  simp only [coding_omega]
  apply forall_congr'
  intro n
  apply forall_congr'
  intro hn
  simp [coding_atomicArguments hL hn]

@[simp] theorem coding_formulas {L : M} (hL : ZFVP.IsLanguageCode L) :
    Coding.formulas mem L = ZFVP.formulaFamily L ∅ := by
  apply setValue_eq
  intro p
  simp only [ZFVP.mem_formulaFamily_iff, coding_formulaClosed hL]
  constructor
  · exact And.right
  · intro h
    exact ⟨h _ (ZFVP.syntaxUniverse_formulaClosed hL ∅), h⟩

end PalomarBridge
