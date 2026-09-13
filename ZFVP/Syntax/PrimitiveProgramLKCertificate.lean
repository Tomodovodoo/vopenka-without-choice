import ZFVP.Syntax.PrimitiveProgramLKRuleCheck

/-! Explicit right-fold traversal of LK certificates, accumulating conclusions and a validity bit. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def lkCertificateStep : PrimitiveProgram :=
  let row := .comp .left .right
  let st := .comp .right .right
  let S := .comp .left st
  let ok := .comp .right st
  let C := .comp .left row
  .pair (listCons C S)
    (allOf [.comp equal (.pair ok (constant 1)),
      .comp equal (.pair (.comp lkRuleCheck (.pair S row)) (constant 1))])

def lkCertificateRun : PrimitiveProgram := listFold (.pair .zero (constant 1)) lkCertificateStep

def lkProofCheck : PrimitiveProgram :=
  let run := .comp lkCertificateRun (.pair .zero .right)
  allOf [.comp equal (.pair (.comp .right run) (constant 1)),
    .comp listMember (.pair .left (.comp .left run))]

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem evalArithmetic_lkCertificateStep (z C w S ok : M) :
    lkCertificateStep.evalArithmetic (Arithmetic.pair z (Arithmetic.pair (Arithmetic.pair C w) (Arithmetic.pair S ok))) =
      Arithmetic.pair (Arithmetic.pair C S + 1)
        (if ok = 1 ∧ lkRuleCheck.evalArithmetic (Arithmetic.pair S (Arithmetic.pair C w)) = 1 then 1 else 0) := by
  by_cases ho : ok = 1 <;>
    by_cases hc : lkRuleCheck.evalArithmetic (Arithmetic.pair S (Arithmetic.pair C w)) = 1 <;>
      simp [lkCertificateStep, listCons, allOf, ho, hc]

@[simp] theorem evalArithmetic_lkCertificateRun_zero (z : M) :
    PrimitiveProgram.lkCertificateRun.evalArithmetic (Arithmetic.pair z 0) = Arithmetic.pair 0 1 := by
  simp [PrimitiveProgram.lkCertificateRun]

theorem evalArithmetic_lkCertificateRun_cons (z C w p : M) :
    PrimitiveProgram.lkCertificateRun.evalArithmetic (Arithmetic.pair z (Arithmetic.pair (Arithmetic.pair C w) p + 1)) =
      Arithmetic.pair (Arithmetic.pair C (Arithmetic.unpair (PrimitiveProgram.lkCertificateRun.evalArithmetic (Arithmetic.pair z p))).1 + 1)
        (if (Arithmetic.unpair (PrimitiveProgram.lkCertificateRun.evalArithmetic (Arithmetic.pair z p))).2 = 1 ∧
          lkRuleCheck.evalArithmetic (Arithmetic.pair
            (Arithmetic.unpair (PrimitiveProgram.lkCertificateRun.evalArithmetic (Arithmetic.pair z p))).1
            (Arithmetic.pair C w)) = 1 then 1 else 0) := by
  rw [PrimitiveProgram.lkCertificateRun, evalArithmetic_listFold_cons]
  change lkCertificateStep.evalArithmetic (Arithmetic.pair z (Arithmetic.pair (Arithmetic.pair C w)
    (PrimitiveProgram.lkCertificateRun.evalArithmetic (Arithmetic.pair z p)))) = _
  conv_lhs => rw [← Arithmetic.pair_unpair (PrimitiveProgram.lkCertificateRun.evalArithmetic (Arithmetic.pair z p))]
  exact evalArithmetic_lkCertificateStep _ _ _ _ _

theorem evalArithmetic_lkCertificateRun_cons_left (z C w p : M) :
    Arithmetic.pi₁ (PrimitiveProgram.lkCertificateRun.evalArithmetic
      (Arithmetic.pair z (Arithmetic.pair (Arithmetic.pair C w) p + 1))) =
      Arithmetic.pair C (Arithmetic.pi₁ (PrimitiveProgram.lkCertificateRun.evalArithmetic (Arithmetic.pair z p))) + 1 := by
  rw [evalArithmetic_lkCertificateRun_cons]
  simp

theorem evalArithmetic_lkCertificateRun_cons_right_eq_one (z C w p : M) :
    Arithmetic.pi₂ (PrimitiveProgram.lkCertificateRun.evalArithmetic
      (Arithmetic.pair z (Arithmetic.pair (Arithmetic.pair C w) p + 1))) = 1 ↔
      Arithmetic.pi₂ (PrimitiveProgram.lkCertificateRun.evalArithmetic (Arithmetic.pair z p)) = 1 ∧
        lkRuleCheck.evalArithmetic (Arithmetic.pair
          (Arithmetic.pi₁ (PrimitiveProgram.lkCertificateRun.evalArithmetic (Arithmetic.pair z p)))
          (Arithmetic.pair C w)) = 1 := by
  rw [evalArithmetic_lkCertificateRun_cons]
  simp

theorem evalArithmetic_lkProofCheck_eq_one (C p : M) :
    lkProofCheck.evalArithmetic (Arithmetic.pair C p) = 1 ↔
      Arithmetic.pi₂ (PrimitiveProgram.lkCertificateRun.evalArithmetic (Arithmetic.pair 0 p)) = 1 ∧
        listMember.evalArithmetic (Arithmetic.pair C
          (Arithmetic.pi₁ (PrimitiveProgram.lkCertificateRun.evalArithmetic (Arithmetic.pair 0 p)))) = 1 := by
  simp [lkProofCheck]

end PrimitiveProgram
end ZFVP
