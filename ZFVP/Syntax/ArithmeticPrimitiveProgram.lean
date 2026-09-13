import ZFVP.Syntax.PrimitiveProgram
import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-! Sigma-one arithmetic formulas for explicit primitive-recursive programs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def arithmeticRecBlueprint (φ ψ : 𝚺₁.Semisentence 2) : PR.Blueprint 1 where
  zero := φ
  succ := .mkSigma “r h i z. ∃ p q, !pairDef q i h ∧ !pairDef p z q ∧ !ψ r p”

def arithmeticFormula : PrimitiveProgram → 𝚺₁.Semisentence 2
  | .zero => .mkSigma “y x. y = 0”
  | .succ => .mkSigma “y x. y = x + 1”
  | .left => .mkSigma pi₁Def.val
  | .right => .mkSigma pi₂Def.val
  | .pair a b => .mkSigma “y x. ∃ u v, !a.arithmeticFormula u x ∧ !b.arithmeticFormula v x ∧ !pairDef y u v”
  | .comp a b => .mkSigma “y x. ∃ u, !b.arithmeticFormula u x ∧ !a.arithmeticFormula y u”
  | .prec a b => .mkSigma “y x. ∃ z n, !pi₁Def z x ∧ !pi₂Def n x ∧
      !(arithmeticRecBlueprint a.arithmeticFormula b.arithmeticFormula).resultDef y n z”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def arithmeticRecConstruction (F G : M → M) (φ ψ : 𝚺₁.Semisentence 2)
    (hF : 𝚺₁.DefinedFunction₁ F φ) (hG : 𝚺₁.DefinedFunction₁ G ψ) :
    PR.Construction M (arithmeticRecBlueprint φ ψ) where
  zero v := F (v 0)
  succ v i h := G (Arithmetic.pair (v 0) (Arithmetic.pair i h))
  zero_defined := hF
  succ_defined := .mk fun v ↦ by simp [arithmeticRecBlueprint, hG.iff]

structure ArithmeticRealization (c : PrimitiveProgram) where
  func : M → M
  defined : 𝚺₁.DefinedFunction₁ func c.arithmeticFormula

noncomputable def arithmeticRealization (c : PrimitiveProgram) : ArithmeticRealization (M := M) c := by
  induction c with
  | zero => exact ⟨fun _ ↦ 0, .mk fun v ↦ by simp [arithmeticFormula]⟩
  | succ => exact ⟨fun x ↦ x + 1, .mk fun v ↦ by simp [arithmeticFormula]⟩
  | left => exact ⟨Arithmetic.pi₁, .mk fun v ↦ by simp [arithmeticFormula, pi₁_defined.iff]⟩
  | right => exact ⟨Arithmetic.pi₂, .mk fun v ↦ by simp [arithmeticFormula, pi₂_defined.iff]⟩
  | pair a b ha hb =>
    exact ⟨fun x ↦ Arithmetic.pair (ha.func x) (hb.func x),
      .mk fun v ↦ by simp [arithmeticFormula, ha.defined.iff, hb.defined.iff]⟩
  | comp a b ha hb =>
    exact ⟨fun x ↦ ha.func (hb.func x),
      .mk fun v ↦ by simp [arithmeticFormula, ha.defined.iff, hb.defined.iff]⟩
  | prec a b ha hb =>
    let C := arithmeticRecConstruction ha.func hb.func a.arithmeticFormula b.arithmeticFormula ha.defined hb.defined
    refine ⟨fun x ↦ C.result ![Arithmetic.pi₁ x] (Arithmetic.pi₂ x), .mk ?_⟩
    intro v
    simp [arithmeticFormula, pi₁_defined.iff, pi₂_defined.iff, C.result_defined_iff,
      Matrix.fun_eq_vec_one]

noncomputable def evalArithmetic (c : PrimitiveProgram) : M → M := c.arithmeticRealization.func

theorem evalArithmetic_defined (c : PrimitiveProgram) :
    𝚺₁.DefinedFunction₁ (c.evalArithmetic : M → M) c.arithmeticFormula := c.arithmeticRealization.defined

theorem eval_arithmeticFormula_iff (c : PrimitiveProgram) (x y : M) :
    c.arithmeticFormula.val.Evalb ![y, x] ↔ y = c.evalArithmetic x := (evalArithmetic_defined c).iff

end PrimitiveProgram
end ZFVP
