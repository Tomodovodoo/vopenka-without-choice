import ZFVP.ModelTheory.PrimitiveProgramAgreement
import ZFVP.Syntax.PrimitiveProgramListLength
import ZFVP.SetTheory.FiniteSequences

/-! Internal finite sequences decoded from all internal natural-number list codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace PrimitiveProgram

theorem evalSet_pair_val (c : PrimitiveProgram) (x y : InternalArithmetic V) :
    c.evalSet (naturalSquarePair (internalArithmeticVal x) (internalArithmeticVal y)) =
      internalArithmeticVal (c.evalArithmetic (Arithmetic.pair x y)) := by
  rw [← internalArithmeticVal_pair, evalArithmetic_agreement]

theorem evalSet_val_eq_zero (c : PrimitiveProgram) (x : InternalArithmetic V) :
    c.evalSet (internalArithmeticVal x) = 0 ↔ c.evalArithmetic x = 0 := by
  rw [← evalArithmetic_agreement, ← internalArithmeticVal_zero, ← internalArithmetic_eq]

theorem evalSet_listLength_subset {x : V} (hx : x ∈ (ω : V)) : listLength.evalSet x ⊆ x := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hx
  rw [← evalArithmetic_agreement, ← internalArithmetic_le]
  exact evalArithmetic_listLength_le u

theorem evalSet_listDrop_ne_zero {x n : V} (hx : x ∈ (ω : V)) (hn : n ∈ (ω : V)) :
    listDrop.evalSet (naturalSquarePair x n) ≠ 0 ↔ n ∈ listLength.evalSet x := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hx
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hn
  rw [← internalArithmeticVal_pair, ne_eq, evalSet_val_eq_zero, ← ne_eq,
    evalArithmetic_listDrop_ne_zero, internalArithmetic_lt, evalArithmetic_agreement]

theorem evalSet_listLength_cons {x xs : V} (hx : x ∈ (ω : V)) (hxs : xs ∈ (ω : V)) :
    listLength.evalSet (SetTheory.succ (naturalSquarePair x xs)) = SetTheory.succ (listLength.evalSet xs) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hx
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hxs
  have he (w : InternalArithmetic V) : internalArithmeticVal (w + 1) = SetTheory.succ (internalArithmeticVal w) := by
    simp only [internalArithmeticVal_add, internalArithmeticVal_one]
    exact ordinalAdd_one_natural (internalArithmeticVal_mem w)
  rw [← internalArithmeticVal_pair, ← he, ← evalArithmetic_agreement,
    evalArithmetic_listLength_cons, he, evalArithmetic_agreement]

end PrimitiveProgram

open PrimitiveProgram

noncomputable def decodedNaturalList (x : V) : V :=
  definableGraph (listLength.evalSet x) (fun i ↦ listGet.evalSet (naturalSquarePair x i)) (by definability)

def decodedNaturalListFormula : SetTheorySemisentence 2 :=
  f“S x. ∀ p, p ∈ S ↔ ∃ l i q y, !listLength.formula l x ∧ i ∈ l ∧
    !naturalSquarePairFormula q x i ∧ !listGet.formula y q ∧ p = !kpair.dfn i y”

theorem mem_decodedNaturalList (x p : V) : p ∈ decodedNaturalList x ↔
    ∃ i ∈ listLength.evalSet x, p = ⟨i, listGet.evalSet (naturalSquarePair x i)⟩ₖ :=
  mem_definableGraph_iff _ _ _ _

instance decodedNaturalList_defined : ℒₛₑₜ-function₁[V] decodedNaturalList via decodedNaturalListFormula :=
  ⟨fun v ↦ by
    simp [decodedNaturalListFormula, (evalSet_defined listLength).iff,
      (evalSet_defined listGet).iff, naturalSquarePair_defined.iff,
      mem_ext_iff (y := decodedNaturalList _), mem_decodedNaturalList]⟩

instance decodedNaturalList_definable : ℒₛₑₜ-function₁[V] decodedNaturalList :=
  decodedNaturalList_defined.to_definable

instance decodedNaturalList_isFunction (x : V) : IsFunction (decodedNaturalList x) :=
  definableGraph_isFunction _ _ _

@[simp] theorem domain_decodedNaturalList (x : V) : domain (decodedNaturalList x) = listLength.evalSet x :=
  domain_definableGraph _ _ _

theorem value_decodedNaturalList {x i : V} (hi : i ∈ listLength.evalSet x) :
    (decodedNaturalList x) ‘ i = listGet.evalSet (naturalSquarePair x i) :=
  value_definableGraph _ _ _ hi

theorem decodedNaturalList_mem_function {x : V} (hx : x ∈ (ω : V)) :
    decodedNaturalList x ∈ (ω : V) ^ listLength.evalSet x := by
  apply definableGraph_mem_function_of_mapsTo
  intro i hi
  exact evalSet_natural listGet (naturalSquarePair_natural hx
    (IsTransitive.transitive _ (evalSet_natural listLength hx) _ hi))

theorem decodedNaturalList_mem_finiteSequences {x : V} (hx : x ∈ (ω : V)) :
    decodedNaturalList x ∈ finiteSequences (ω : V) :=
  (mem_finiteSequences_iff _ _).mpr
    ⟨listLength.evalSet x, evalSet_natural listLength hx, decodedNaturalList_mem_function hx⟩

end ZFVP
