import ZFVP.Syntax.PrimitiveProgramFormulaTransformLimits

/-! Constructor equations for formula transformation with any supplied argument program. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem evalArithmetic_formulaTransformCode_tagged (arguments : PrimitiveProgram) (s d t c : M) :
    (formulaTransformCode arguments).evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair t c + 1))) =
      (arithmeticFormulaTransformValue arguments) s d t c
        (fun child depth ↦ (formulaTransformCode arguments).evalArithmetic (Arithmetic.pair s (Arithmetic.pair depth child))) := by
  rw [(evalArithmetic_formulaTransformCode arguments),
    (evalArithmetic_formulaTransformBounded_tagged arguments) s _ t c d le_self_add]
  have hc : c < Arithmetic.pair t c + 1 := lt_succ_iff_le.mpr (le_pair_right t c)
  have hl : Arithmetic.pi₁ c < Arithmetic.pair t c + 1 := lt_of_le_of_lt (pi₁_le_self c) hc
  have hr : Arithmetic.pi₂ c < Arithmetic.pair t c + 1 := lt_of_le_of_lt (pi₂_le_self c) hc
  have hb (i : M) (hi : i < Arithmetic.pair t c + 1) : d + i ≤ d + (Arithmetic.pair t c + 1) :=
    add_le_add_right (le_of_lt hi) d
  have hq : d + 1 + c ≤ d + (Arithmetic.pair t c + 1) := by
    have he : d + 1 + c = d + (c + 1) := by ac_rfl
    rw [he]
    exact add_le_add_right (succ_le_iff_lt.mpr hc) d
  simp only [arithmeticFormulaTransformValue,
    (evalArithmetic_formulaTransformBounded_eq_code arguments) s _ _ d (hb _ hl),
    (evalArithmetic_formulaTransformBounded_eq_code arguments) s _ _ d (hb _ hr),
    (evalArithmetic_formulaTransformBounded_eq_code arguments) s _ c (d + 1) hq]

@[simp] theorem evalArithmetic_formulaTransformCode_zero (arguments : PrimitiveProgram) (s d : M) :
    (formulaTransformCode arguments).evalArithmetic (Arithmetic.pair s (Arithmetic.pair d 0)) = 0 := by
  rw [(evalArithmetic_formulaTransformCode arguments), (evalArithmetic_formulaTransformBounded arguments) s _ 0 d le_self_add]
  simp

@[simp] theorem evalArithmetic_formulaTransformCode_rel (arguments : PrimitiveProgram) (s d c : M) :
    (formulaTransformCode arguments).evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair 0 c + 1))) =
      Arithmetic.pair 0 (Arithmetic.pair 2 (Arithmetic.pair (Arithmetic.pi₁ (Arithmetic.pi₂ c))
        (arguments.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pi₂ (Arithmetic.pi₂ c))))))) + 1 := by
  simp only [(evalArithmetic_formulaTransformCode_tagged arguments), arithmeticFormulaTransformValue, ite_true]

@[simp] theorem evalArithmetic_formulaTransformCode_nrel (arguments : PrimitiveProgram) (s d c : M) :
    (formulaTransformCode arguments).evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair 1 c + 1))) =
      Arithmetic.pair 1 (Arithmetic.pair 2 (Arithmetic.pair (Arithmetic.pi₁ (Arithmetic.pi₂ c))
        (arguments.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pi₂ (Arithmetic.pi₂ c))))))) + 1 := by
  rw [(evalArithmetic_formulaTransformCode_tagged arguments)]
  simp [arithmeticFormulaTransformValue]

@[simp] theorem evalArithmetic_formulaTransformCode_verum (arguments : PrimitiveProgram) (s d c : M) :
    (formulaTransformCode arguments).evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair 2 c + 1))) =
      Arithmetic.pair 2 0 + 1 := by
  rw [(evalArithmetic_formulaTransformCode_tagged arguments)]
  simp [arithmeticFormulaTransformValue]

@[simp] theorem evalArithmetic_formulaTransformCode_falsum (arguments : PrimitiveProgram) (s d c : M) :
    (formulaTransformCode arguments).evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair 3 c + 1))) =
      Arithmetic.pair 3 0 + 1 := by
  rw [(evalArithmetic_formulaTransformCode_tagged arguments)]
  simp [arithmeticFormulaTransformValue]

@[simp] theorem evalArithmetic_formulaTransformCode_and (arguments : PrimitiveProgram) (s d a b : M) :
    (formulaTransformCode arguments).evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair 4 (Arithmetic.pair a b) + 1))) =
      Arithmetic.pair 4 (Arithmetic.pair
        ((formulaTransformCode arguments).evalArithmetic (Arithmetic.pair s (Arithmetic.pair d a)))
        ((formulaTransformCode arguments).evalArithmetic (Arithmetic.pair s (Arithmetic.pair d b)))) + 1 := by
  rw [(evalArithmetic_formulaTransformCode_tagged arguments)]
  simp [arithmeticFormulaTransformValue]

@[simp] theorem evalArithmetic_formulaTransformCode_or (arguments : PrimitiveProgram) (s d a b : M) :
    (formulaTransformCode arguments).evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair 5 (Arithmetic.pair a b) + 1))) =
      Arithmetic.pair 5 (Arithmetic.pair
        ((formulaTransformCode arguments).evalArithmetic (Arithmetic.pair s (Arithmetic.pair d a)))
        ((formulaTransformCode arguments).evalArithmetic (Arithmetic.pair s (Arithmetic.pair d b)))) + 1 := by
  rw [(evalArithmetic_formulaTransformCode_tagged arguments)]
  simp [arithmeticFormulaTransformValue]

@[simp] theorem evalArithmetic_formulaTransformCode_all (arguments : PrimitiveProgram) (s d a : M) :
    (formulaTransformCode arguments).evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair 6 a + 1))) =
      Arithmetic.pair 6 ((formulaTransformCode arguments).evalArithmetic (Arithmetic.pair s (Arithmetic.pair (d + 1) a))) + 1 := by
  rw [(evalArithmetic_formulaTransformCode_tagged arguments)]
  simp [arithmeticFormulaTransformValue]

@[simp] theorem evalArithmetic_formulaTransformCode_exs (arguments : PrimitiveProgram) (s d a : M) :
    (formulaTransformCode arguments).evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair 7 a + 1))) =
      Arithmetic.pair 7 ((formulaTransformCode arguments).evalArithmetic (Arithmetic.pair s (Arithmetic.pair (d + 1) a))) + 1 := by
  rw [(evalArithmetic_formulaTransformCode_tagged arguments)]
  simp [arithmeticFormulaTransformValue]

end PrimitiveProgram
end ZFVP