import ZFVP.ModelTheory.InternalFormulaTransformSubstitution
import ZFVP.Syntax.PrimitiveProgramReindexVariables

/-! Internal bound-variable renaming, its binder equations, and preservation of the target context. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def naturalReindexVariable (r d i : V) : V :=
  reindexVariable.evalSet (naturalSquarePair r (naturalSquarePair d i))

instance naturalReindexVariable_definable : ℒₛₑₜ-function₃[V] naturalReindexVariable := by
  unfold naturalReindexVariable
  definability

theorem naturalReindexVariable_natural {r d i : V}
    (hr : r ∈ (ω : V)) (hd : d ∈ (ω : V)) (hi : i ∈ (ω : V)) : naturalReindexVariable r d i ∈ (ω : V) :=
  evalSet_natural reindexVariable (naturalSquarePair_natural hr (naturalSquarePair_natural hd hi))

theorem naturalReindexVariable_val (r d i : InternalArithmetic V) :
    naturalReindexVariable (internalArithmeticVal r) (internalArithmeticVal d) (internalArithmeticVal i) =
      internalArithmeticVal (arithmeticReindexVariable r d i) := by
  unfold naturalReindexVariable
  rw [← internalArithmeticVal_pair, evalSet_pair_val, evalArithmetic_reindexVariable]

theorem naturalReindexVariable_below {r d i : V}
    (hr : r ∈ (ω : V)) (hd : d ∈ (ω : V)) (hi : i ∈ d) : naturalReindexVariable r d i = i := by
  have hiω := IsTransitive.transitive _ hd _ hi
  obtain ⟨r₀, rfl⟩ := internalArithmeticVal_surjective hr
  obtain ⟨d₀, rfl⟩ := internalArithmeticVal_surjective hd
  obtain ⟨i₀, rfl⟩ := internalArithmeticVal_surjective hiω
  rw [naturalReindexVariable_val, arithmeticReindexVariable_below r₀ ((internalArithmetic_lt i₀ d₀).mpr hi)]

theorem naturalReindexVariable_zeroDepth {r i : V} (hr : r ∈ (ω : V))
    (hi : i ∈ listLength.evalSet r) : naturalReindexVariable r 0 i = listGet.evalSet (naturalSquarePair r i) := by
  have hiω := IsTransitive.transitive _ (evalSet_natural listLength hr) _ hi
  obtain ⟨r₀, rfl⟩ := internalArithmeticVal_surjective hr
  obtain ⟨i₀, rfl⟩ := internalArithmeticVal_surjective hiω
  have hi' : i₀ < listLength.evalArithmetic r₀ := by
    rw [internalArithmetic_lt, evalArithmetic_agreement]
    exact hi
  have h := congrArg internalArithmeticVal (arithmeticReindexVariable_zeroDepth r₀ i₀ hi')
  simpa only [← naturalReindexVariable_val, internalArithmeticVal_zero, evalArithmetic_agreement,
    internalArithmeticVal_pair] using h

theorem naturalReindexVariable_lift_zero {r d : V} (hr : r ∈ (ω : V)) (hd : d ∈ (ω : V)) :
    naturalReindexVariable r (SetTheory.succ d) 0 = 0 := by
  obtain ⟨r₀, rfl⟩ := internalArithmeticVal_surjective hr
  obtain ⟨d₀, rfl⟩ := internalArithmeticVal_surjective hd
  have h := congrArg internalArithmeticVal (arithmeticReindexVariable_lift_zero r₀ d₀)
  simpa only [← naturalReindexVariable_val, internalArithmeticVal_zero, internalArithmeticVal_succ] using h

theorem naturalReindexVariable_lift_succ {r d i : V}
    (hr : r ∈ (ω : V)) (hd : d ∈ (ω : V)) (hi : i ∈ (ω : V)) :
    naturalReindexVariable r (SetTheory.succ d) (SetTheory.succ i) = SetTheory.succ (naturalReindexVariable r d i) := by
  obtain ⟨r₀, rfl⟩ := internalArithmeticVal_surjective hr
  obtain ⟨d₀, rfl⟩ := internalArithmeticVal_surjective hd
  obtain ⟨i₀, rfl⟩ := internalArithmeticVal_surjective hi
  have h := congrArg internalArithmeticVal (arithmeticReindexVariable_lift_succ r₀ d₀ i₀)
  simpa only [internalArithmeticVal_succ, ← naturalReindexVariable_val] using h

theorem naturalReindexVariable_bound {r m d i : V}
    (hr : r ∈ (ω : V)) (hm : m ∈ (ω : V)) (hd : d ∈ (ω : V))
    (hR : ∀ j ∈ listLength.evalSet r, listGet.evalSet (naturalSquarePair r j) ∈ m)
    (hi : i ∈ ordinalAdd (listLength.evalSet r) d) : naturalReindexVariable r d i ∈ ordinalAdd m d := by
  have hiω := IsTransitive.transitive _ (ordinalAdd_natural (evalSet_natural listLength hr) hd) _ hi
  obtain ⟨r₀, rfl⟩ := internalArithmeticVal_surjective hr
  obtain ⟨m₀, rfl⟩ := internalArithmeticVal_surjective hm
  obtain ⟨d₀, rfl⟩ := internalArithmeticVal_surjective hd
  obtain ⟨i₀, rfl⟩ := internalArithmeticVal_surjective hiω
  have hR' : ∀ j < listLength.evalArithmetic r₀, listGet.evalArithmetic (Arithmetic.pair r₀ j) < m₀ := by
    intro j hj
    apply (internalArithmetic_lt _ _).mpr
    rw [evalArithmetic_agreement, internalArithmeticVal_pair]
    apply hR
    rw [← evalArithmetic_agreement, ← internalArithmetic_lt]
    exact hj
  have hi' : i₀ < listLength.evalArithmetic r₀ + d₀ := by
    rw [internalArithmetic_lt, internalArithmeticVal_add, evalArithmetic_agreement]
    exact hi
  rw [naturalReindexVariable_val, ← internalArithmeticVal_add, ← internalArithmetic_lt]
  exact arithmeticReindexVariable_bound hR' hi'

theorem evalSet_reindexTerm_bound {r d i : V}
    (hr : r ∈ (ω : V)) (hd : d ∈ (ω : V)) (hi : i ∈ (ω : V)) :
    reindexTerm.evalSet (naturalSquarePair r (naturalSquarePair d (SetTheory.succ (naturalSquarePair 0 i)))) =
      SetTheory.succ (naturalSquarePair 0 (naturalReindexVariable r d i)) := by
  obtain ⟨r₀, rfl⟩ := internalArithmeticVal_surjective hr
  obtain ⟨d₀, rfl⟩ := internalArithmeticVal_surjective hd
  obtain ⟨i₀, rfl⟩ := internalArithmeticVal_surjective hi
  have h := congrArg internalArithmeticVal (evalArithmetic_reindexTerm_bound r₀ d₀ i₀)
  simpa only [evalArithmetic_agreement, internalArithmeticVal_pair, internalArithmeticVal_succ,
    internalArithmeticVal_zero, ← naturalReindexVariable_val] using h

end ZFVP
