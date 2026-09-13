import ZFVP.Syntax.ArithmeticPrimitiveProgram

/-! Exact program equations in every model of Sigma-one induction. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_zero (x : M) : PrimitiveProgram.zero.evalArithmetic x = 0 := rfl
@[simp] theorem evalArithmetic_succ (x : M) : PrimitiveProgram.succ.evalArithmetic x = x + 1 := rfl
@[simp] theorem evalArithmetic_left (x : M) : PrimitiveProgram.left.evalArithmetic x = Arithmetic.pi₁ x := rfl
@[simp] theorem evalArithmetic_right (x : M) : PrimitiveProgram.right.evalArithmetic x = Arithmetic.pi₂ x := rfl
@[simp] theorem evalArithmetic_pair (a b : PrimitiveProgram) (x : M) :
    (PrimitiveProgram.pair a b).evalArithmetic x = Arithmetic.pair (a.evalArithmetic x) (b.evalArithmetic x) := rfl
@[simp] theorem evalArithmetic_comp (a b : PrimitiveProgram) (x : M) :
    (PrimitiveProgram.comp a b).evalArithmetic x = a.evalArithmetic (b.evalArithmetic x) := rfl

noncomputable def recConstruction (a b : PrimitiveProgram) :
    PR.Construction M (arithmeticRecBlueprint a.arithmeticFormula b.arithmeticFormula) :=
  arithmeticRecConstruction a.evalArithmetic b.evalArithmetic a.arithmeticFormula b.arithmeticFormula
    (evalArithmetic_defined a) (evalArithmetic_defined b)

theorem evalArithmetic_prec (a b : PrimitiveProgram) (x : M) :
    (PrimitiveProgram.prec a b).evalArithmetic x =
      (recConstruction a b).result ![Arithmetic.pi₁ x] (Arithmetic.pi₂ x) := rfl

theorem evalArithmetic_prec_pair (a b : PrimitiveProgram) (z n : M) :
    (PrimitiveProgram.prec a b).evalArithmetic (Arithmetic.pair z n) = (recConstruction a b).result ![z] n := by
  simp only [evalArithmetic_prec, Arithmetic.pi₁_pair, Arithmetic.pi₂_pair]

@[simp] theorem evalArithmetic_prec_zero (a b : PrimitiveProgram) (z : M) :
    (PrimitiveProgram.prec a b).evalArithmetic (Arithmetic.pair z 0) = a.evalArithmetic z := by
  rw [evalArithmetic_prec_pair, PR.Construction.result_zero]
  rfl

theorem evalArithmetic_prec_succ (a b : PrimitiveProgram) (z n : M) :
    (PrimitiveProgram.prec a b).evalArithmetic (Arithmetic.pair z (n + 1)) =
      b.evalArithmetic (Arithmetic.pair z (Arithmetic.pair n
        ((PrimitiveProgram.prec a b).evalArithmetic (Arithmetic.pair z n)))) := by
  rw [evalArithmetic_prec_pair, PR.Construction.result_succ, evalArithmetic_prec_pair]
  rfl

theorem eval_recConstruction_result (a b : PrimitiveProgram) (r n z : M) :
    (arithmeticRecBlueprint a.arithmeticFormula b.arithmeticFormula).resultDef.val.Evalb ![r, n, z] ↔
      r = (recConstruction a b).result ![z] n := by
  simpa [Matrix.fun_eq_vec_one] using (recConstruction a b).result_defined_iff ![r, n, z]

end PrimitiveProgram
end ZFVP
