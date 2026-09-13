import ZFVP.Syntax.ArithmeticPrimitiveProgramStandard
import Foundation.FirstOrder.Arithmetic.Definability.Absoluteness

/-! Every arithmetic model computes the same values on standard program inputs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem arithmeticPair_natCast (a b : ℕ) : Arithmetic.pair (a : M) (b : M) = (Nat.pair a b : M) := by
  have h : pairDef.val.Evalb ![Nat.pair a b, a, b] := by
    simp [← arithmeticPair_nat]
  have ht := bold_sigma_one_completeness' (M := M) (σ := pairDef.val)
    (by simp) h
  simpa [numeral_eq_natCast, Function.comp_def, eq_comm] using ht

namespace PrimitiveProgram

theorem evalArithmetic_natCast (c : PrimitiveProgram) (n : ℕ) : c.evalArithmetic (n : M) = (c.eval n : M) := by
  have h := (eval_arithmeticFormula_nat c n (c.eval n)).mpr rfl
  have ht := bold_sigma_one_completeness' (M := M) (σ := c.arithmeticFormula.val) (by simp) h
  have he : (fun i : Fin 2 ↦ (![c.eval n, n] i : M)) = ![(c.eval n : M), (n : M)] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  have hv : c.arithmeticFormula.val.Evalb ![(c.eval n : M), (n : M)] := by
    simpa only [numeral_eq_natCast, Function.comp_def, he] using ht
  exact ((eval_arithmeticFormula_iff c _ _).mp hv).symm

end PrimitiveProgram
end ZFVP
