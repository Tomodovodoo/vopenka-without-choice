import ZFVP.Syntax.PrimitiveProgramFormulaTransform
import ZFVP.Syntax.PrimitiveProgramListExt

/-! Formula transformation is independent of the auxiliary table limit once depth plus code fits. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem formulaTransformBounded_limit_independent (arguments : PrimitiveProgram) (n s d D E : M)
    (hD : d + n ≤ D) (hE : d + n ≤ E) :
    (formulaTransformBounded arguments).evalArithmetic (Arithmetic.pair (Arithmetic.pair s D) (Arithmetic.pair n d)) =
      (formulaTransformBounded arguments).evalArithmetic (Arithmetic.pair (Arithmetic.pair s E) (Arithmetic.pair n d)) := by
  induction n using ISigma1.pi1_order_induction generalizing s d D E
  · definability
  case ind n ih =>
    have hdD : d ≤ D := le_trans le_self_add hD
    have hdE : d ≤ E := le_trans le_self_add hE
    rcases listCode_cases n with (rfl | ⟨t, a, rfl⟩)
    · simp [(evalArithmetic_formulaTransformBounded arguments) s D 0 d hdD, (evalArithmetic_formulaTransformBounded arguments) s E 0 d hdE]
    have ha : a < Arithmetic.pair t a + 1 := lt_succ_iff_le.mpr (le_pair_right t a)
    have hl : Arithmetic.pi₁ a < Arithmetic.pair t a + 1 := lt_of_le_of_lt (pi₁_le_self a) ha
    have hr : Arithmetic.pi₂ a < Arithmetic.pair t a + 1 := lt_of_le_of_lt (pi₂_le_self a) ha
    have hbD (i : M) (hi : i < Arithmetic.pair t a + 1) : d + i ≤ D :=
      le_trans (add_le_add_right (le_of_lt hi) d) hD
    have hbE (i : M) (hi : i < Arithmetic.pair t a + 1) : d + i ≤ E :=
      le_trans (add_le_add_right (le_of_lt hi) d) hE
    have hq : d + 1 + a ≤ d + (Arithmetic.pair t a + 1) := by
      have he : d + 1 + a = d + (a + 1) := by ac_rfl
      rw [he]
      exact add_le_add_right (succ_le_iff_lt.mpr ha) d
    have il := ih (Arithmetic.pi₁ a) hl s d D E (hbD _ hl) (hbE _ hl)
    have ir := ih (Arithmetic.pi₂ a) hr s d D E (hbD _ hr) (hbE _ hr)
    have iq := ih a ha s (d + 1) D E (le_trans hq hD) (le_trans hq hE)
    rw [(evalArithmetic_formulaTransformBounded_tagged arguments) s D t a d hdD,
      (evalArithmetic_formulaTransformBounded_tagged arguments) s E t a d hdE]
    simp only [arithmeticFormulaTransformValue, il, ir, iq]

theorem evalArithmetic_formulaTransformBounded_eq_code (arguments : PrimitiveProgram) (s D n d : M) (hD : d + n ≤ D) :
    (formulaTransformBounded arguments).evalArithmetic (Arithmetic.pair (Arithmetic.pair s D) (Arithmetic.pair n d)) =
      (formulaTransformCode arguments).evalArithmetic (Arithmetic.pair s (Arithmetic.pair d n)) := by
  rw [(evalArithmetic_formulaTransformCode arguments)]
  exact (formulaTransformBounded_limit_independent arguments) n s d D (d + n) hD (le_refl _)

end PrimitiveProgram
end ZFVP