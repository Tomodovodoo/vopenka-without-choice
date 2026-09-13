import ZFVP.ModelTheory.NaturalSyntaxLeaves
import ZFVP.SetTheory.UniformRecursion

/-! A uniform set-valued decoder for natural-number formula trees. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def naturalFormulaDecodeStep (g : V) : V := by
  classical
  let n := domain g
  let t := listHead.evalSet n
  let c := listTail.evalSet n
  let r := relationToken (naturalSquareLeft (naturalSquareRight c))
  let a := decodedNaturalArguments (naturalSquareRight (naturalSquareRight c))
  exact if n = 0 then ∅ else
    if t = 0 then atomCode r a else
    if t = 1 then negAtomCode r a else
    if t = 2 then truthCode else
    if t = 3 then falsityCode else
    if t = 4 then andCode (g ‘ (naturalSquareLeft c)) (g ‘ (naturalSquareRight c)) else
    if t = 5 then orCode (g ‘ (naturalSquareLeft c)) (g ‘ (naturalSquareRight c)) else
    if t = 6 then allCode (g ‘ c) else
    if t = 7 then existsCode (g ‘ c) else ∅

def naturalFormulaDecodeStepFormula : SetTheorySemisentence 2 :=
  f“y g. ∃ n t c r a, n = !domain.dfn g ∧ !listHead.formula t n ∧ !listTail.formula c n ∧
    !relationTokenFormula r (!naturalSquareLeftFormula (!naturalSquareRightFormula c)) ∧
    !decodedNaturalArgumentsFormula a (!naturalSquareRightFormula (!naturalSquareRightFormula c)) ∧
    ((n = !isEmpty ∧ y = !isEmpty) ∨ (n ≠ !isEmpty ∧
    ((t = !isEmpty ∧ !atomCodeFormula y r a) ∨ (t ≠ !isEmpty ∧
    ((t = !(numeralFormula 1) ∧ !negAtomCodeFormula y r a) ∨ (t ≠ !(numeralFormula 1) ∧
    ((t = !(numeralFormula 2) ∧ !truthCodeFormula y) ∨ (t ≠ !(numeralFormula 2) ∧
    ((t = !(numeralFormula 3) ∧ !falsityCodeFormula y) ∨ (t ≠ !(numeralFormula 3) ∧
    ((t = !(numeralFormula 4) ∧ !andCodeFormula y (!value.dfn g (!naturalSquareLeftFormula c)) (!value.dfn g (!naturalSquareRightFormula c))) ∨ (t ≠ !(numeralFormula 4) ∧
    ((t = !(numeralFormula 5) ∧ !orCodeFormula y (!value.dfn g (!naturalSquareLeftFormula c)) (!value.dfn g (!naturalSquareRightFormula c))) ∨ (t ≠ !(numeralFormula 5) ∧
    ((t = !(numeralFormula 6) ∧ !allCodeFormula y (!value.dfn g c)) ∨ (t ≠ !(numeralFormula 6) ∧
    ((t = !(numeralFormula 7) ∧ !existsCodeFormula y (!value.dfn g c)) ∨ (t ≠ !(numeralFormula 7) ∧ y = !isEmpty))))))))))))))))))”

instance naturalFormulaDecodeStep_defined :
    ℒₛₑₜ-function₁[V] naturalFormulaDecodeStep via naturalFormulaDecodeStepFormula :=
  ⟨fun v ↦ by
    classical
    change naturalFormulaDecodeStepFormula.Evalb v ↔ v 0 = naturalFormulaDecodeStep (v 1)
    simp [naturalFormulaDecodeStepFormula, (evalSet_defined listHead).iff,
      (evalSet_defined listTail).iff, -ne_empty_iff_isNonempty]
    unfold naturalFormulaDecodeStep
    dsimp only
    split_ifs <;> simp_all [zero_def, -ne_empty_iff_isNonempty]⟩

instance naturalFormulaDecodeStep_definable : ℒₛₑₜ-function₁[V] naturalFormulaDecodeStep :=
  naturalFormulaDecodeStep_defined.to_definable

noncomputable def decodedNaturalFormula : V → V :=
  Replacement.transfiniteRec naturalFormulaDecodeStep naturalFormulaDecodeStep_definable

def decodedNaturalFormulaFormula : SetTheorySemisentence 2 :=
  transfiniteRecFormula naturalFormulaDecodeStepFormula

instance decodedNaturalFormula_defined :
    ℒₛₑₜ-function₁[V] decodedNaturalFormula via decodedNaturalFormulaFormula :=
  transfiniteRecFormula_defined naturalFormulaDecodeStep naturalFormulaDecodeStepFormula

instance decodedNaturalFormula_definable : ℒₛₑₜ-function₁[V] decodedNaturalFormula :=
  decodedNaturalFormula_defined.to_definable

theorem decodedNaturalFormula_unfold {n : V} (hn : n ∈ (ω : V)) :
    decodedNaturalFormula n = naturalFormulaDecodeStep
      (definableGraph n decodedNaturalFormula decodedNaturalFormula_definable) := by
  have : IsOrdinal n := IsOrdinal.of_mem hn
  exact Replacement.transfiniteRec_spec naturalFormulaDecodeStep naturalFormulaDecodeStep_definable
    (IsOrdinal.toOrdinal n)

end ZFVP
