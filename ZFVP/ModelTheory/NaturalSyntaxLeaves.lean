import ZFVP.ModelTheory.InternalProgramListExt
import ZFVP.Syntax.UniformFormulaCodes
import ZFVP.Syntax.FoundationEncoding

/-! Uniform decoding of natural-number variable and binary-argument codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace PrimitiveProgram

theorem evalSet_listHead_cons {x xs : V} (hx : x ∈ (ω : V)) (hxs : xs ∈ (ω : V)) :
    listHead.evalSet (SetTheory.succ (naturalSquarePair x xs)) = x := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hx
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hxs
  rw [← internalArithmeticVal_pair, ← internalArithmeticVal_succ, ← evalArithmetic_agreement,
    evalArithmetic_listHead_cons]

theorem evalSet_listTail_cons {x xs : V} (hx : x ∈ (ω : V)) (hxs : xs ∈ (ω : V)) :
    listTail.evalSet (SetTheory.succ (naturalSquarePair x xs)) = xs := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hx
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hxs
  rw [← internalArithmeticVal_pair, ← internalArithmeticVal_succ, ← evalArithmetic_agreement,
    evalArithmetic_listTail_cons]

end PrimitiveProgram

open PrimitiveProgram

noncomputable def decodedNaturalTerm (n : V) : V := by
  classical
  exact if n = 0 then ∅ else
    if listHead.evalSet n = 0 then boundVarCode (listTail.evalSet n) else
    if listHead.evalSet n = 1 then freeVarCode (listTail.evalSet n) else ∅

def decodedNaturalTermFormula : SetTheorySemisentence 2 :=
  f“y n. ∃ t c, !listHead.formula t n ∧ !listTail.formula c n ∧
    ((n = !isEmpty ∧ y = !isEmpty) ∨
     (n ≠ !isEmpty ∧ ((t = !isEmpty ∧ !boundVarCodeFormula y c) ∨
       (t = !(numeralFormula 1) ∧ !freeVarCodeFormula y c) ∨
       (t ≠ !isEmpty ∧ t ≠ !(numeralFormula 1) ∧ y = !isEmpty))))”

instance decodedNaturalTerm_defined : ℒₛₑₜ-function₁[V] decodedNaturalTerm via decodedNaturalTermFormula :=
  ⟨fun v ↦ by
    classical
    have h01 : (∅ : V) ≠ 1 := zero_ne_one
    unfold decodedNaturalTerm
    dsimp only
    split_ifs <;> simp_all [decodedNaturalTermFormula, (evalSet_defined listHead).iff,
      (evalSet_defined listTail).iff, zero_def, -ne_empty_iff_isNonempty]⟩

instance decodedNaturalTerm_definable : ℒₛₑₜ-function₁[V] decodedNaturalTerm :=
  decodedNaturalTerm_defined.to_definable

theorem naturalCons_ne_zero {x xs : V} : SetTheory.succ (naturalSquarePair x xs) ≠ (0 : V) := by
  intro he
  have hm : naturalSquarePair x xs ∈ SetTheory.succ (naturalSquarePair x xs) := by simp
  simp [he, zero_def] at hm

@[simp] theorem decodedNaturalTerm_bound {i : V} (hi : i ∈ (ω : V)) :
    decodedNaturalTerm (SetTheory.succ (naturalSquarePair 0 i)) = boundVarCode i := by
  simp [decodedNaturalTerm, naturalCons_ne_zero, evalSet_listHead_cons (show (0 : V) ∈ (ω : V) by simp [zero_def]) hi,
    evalSet_listTail_cons (show (0 : V) ∈ (ω : V) by simp [zero_def]) hi]

@[simp] theorem decodedNaturalTerm_free {i : V} (hi : i ∈ (ω : V)) :
    decodedNaturalTerm (SetTheory.succ (naturalSquarePair 1 i)) = freeVarCode i := by
  simp [decodedNaturalTerm, naturalCons_ne_zero, evalSet_listHead_cons (show (1 : V) ∈ (ω : V) by simp) hi,
    evalSet_listTail_cons (show (1 : V) ∈ (ω : V) by simp) hi]

noncomputable def decodedNaturalArguments (v : V) : V :=
  standardTuple ![decodedNaturalTerm (listHead.evalSet v),
    decodedNaturalTerm (listHead.evalSet (listTail.evalSet v))]

def decodedNaturalArgumentsFormula : SetTheorySemisentence 2 :=
  f“a v. ∀ p, p ∈ a ↔
    p = !kpair.dfn (!isEmpty) (!decodedNaturalTermFormula (!listHead.formula v)) ∨
    p = !kpair.dfn (!(numeralFormula 1)) (!decodedNaturalTermFormula (!listHead.formula (!listTail.formula v)))”

instance decodedNaturalArguments_defined :
    ℒₛₑₜ-function₁[V] decodedNaturalArguments via decodedNaturalArgumentsFormula :=
  ⟨fun v ↦ by
    change decodedNaturalArgumentsFormula.Evalb v ↔ v 0 = decodedNaturalArguments (v 1)
    rw [mem_ext_iff]
    simp [decodedNaturalArgumentsFormula, decodedNaturalArguments, mem_standardTuple_iff, Fin.exists_fin_two, zero_def]⟩

instance decodedNaturalArguments_definable : ℒₛₑₜ-function₁[V] decodedNaturalArguments :=
  decodedNaturalArguments_defined.to_definable

end ZFVP
