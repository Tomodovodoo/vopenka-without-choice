import ZFVP.Syntax.PrimitiveProgramLKRuleCore

/-! The local LK checker validates every decoded formula and sequent before checking its rule. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def lkRuleInputs : PrimitiveProgram :=
  let S := .left
  let C := .comp .left .right
  let w := .comp .right .right
  let w1 := .comp .right w
  let φ := .comp .left w1
  let w2 := .comp .right w1
  let ψ := .comp .left w2
  let w3 := .comp .right w2
  let θ := .comp .left w3
  let w4 := .comp .right w3
  let w5 := .comp .right w4
  let Γ := .comp .left w5
  let Δ := .comp .right w5
  let seq := fun p ↦ .comp (sequentCheck true) (.pair .zero p)
  let formula := fun n p ↦ .comp (formulaCheck true) (.pair (constant n) p)
  allOf [seq C,
    .comp (listAll (.comp (sequentCheck true) (.pair .zero .right))) (.pair .zero S),
    formula 0 φ, formula 0 ψ, formula 1 θ, seq Γ, seq Δ]

def lkRuleCheck : PrimitiveProgram := allOf [lkRuleInputs, lkRuleCore]

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def arithmeticLKInputs (S C φ ψ θ Γ Δ : M) : Prop :=
  (sequentCheck true).evalArithmetic (Arithmetic.pair 0 C) = 1 ∧
  (∀ i < listLength.evalArithmetic S,
    (sequentCheck true).evalArithmetic (Arithmetic.pair 0 (listGet.evalArithmetic (Arithmetic.pair S i))) = 1) ∧
  (formulaCheck true).evalArithmetic (Arithmetic.pair 0 φ) = 1 ∧
  (formulaCheck true).evalArithmetic (Arithmetic.pair 0 ψ) = 1 ∧
  (formulaCheck true).evalArithmetic (Arithmetic.pair 1 θ) = 1 ∧
  (sequentCheck true).evalArithmetic (Arithmetic.pair 0 Γ) = 1 ∧
  (sequentCheck true).evalArithmetic (Arithmetic.pair 0 Δ) = 1

theorem evalArithmetic_lkRuleInputs_ne_zero (S C tag φ ψ θ k Γ Δ : M) :
    lkRuleInputs.evalArithmetic (Arithmetic.pair S (Arithmetic.pair C (Arithmetic.pair tag
      (Arithmetic.pair φ (Arithmetic.pair ψ (Arithmetic.pair θ (Arithmetic.pair k (Arithmetic.pair Γ Δ)))))))) ≠ 0 ↔
      arithmeticLKInputs S C φ ψ θ Γ Δ := by
  simp [lkRuleInputs, arithmeticLKInputs]

theorem evalArithmetic_lkRuleCheck_eq_one (S C tag φ ψ θ k Γ Δ : M) :
    lkRuleCheck.evalArithmetic (Arithmetic.pair S (Arithmetic.pair C (Arithmetic.pair tag
      (Arithmetic.pair φ (Arithmetic.pair ψ (Arithmetic.pair θ (Arithmetic.pair k (Arithmetic.pair Γ Δ)))))))) = 1 ↔
      arithmeticLKInputs S C φ ψ θ Γ Δ ∧ arithmeticLKRuleCore S C tag φ ψ θ k Γ Δ := by
  simp [lkRuleCheck, evalArithmetic_lkRuleInputs_ne_zero, evalArithmetic_lkRuleCore_ne_zero]

end PrimitiveProgram
end ZFVP
