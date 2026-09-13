import ZFVP.Syntax.PrimitiveProgramBooleanChecks
import ZFVP.Syntax.PrimitiveProgramSequentOperations

/-! An explicit primitive program for the eight local LK rule branches. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def listCons (x xs : PrimitiveProgram) : PrimitiveProgram := .comp .succ (.pair x xs)

def lkRuleCore : PrimitiveProgram :=
  let S := .left
  let C := .comp .left .right
  let w := .comp .right .right
  let tag := .comp .left w
  let w1 := .comp .right w
  let φ := .comp .left w1
  let w2 := .comp .right w1
  let ψ := .comp .left w2
  let w3 := .comp .right w2
  let θ := .comp .left w3
  let w4 := .comp .right w3
  let k := .comp .left w4
  let w5 := .comp .right w4
  let Γ := .comp .left w5
  let Δ := .comp .right w5
  let eq := fun a b ↦ .comp equal (.pair a b)
  let mem := fun a ↦ .comp listMember (.pair a S)
  let neg := .comp negateCode φ
  let rwθ := fun mode ↦ .comp proofRewriteAtZero (.pair mode θ)
  ifEqual tag (constant 0) (eq C (listCons φ (listCons neg .zero)))
    (ifEqual tag (constant 1)
      (allOf [mem (listCons φ Γ), mem (listCons neg Δ), eq C (.comp listAppend (.pair Δ Γ))])
    (ifEqual tag (constant 2)
      (allOf [mem Δ, .comp listSubset (.pair Δ C)])
    (ifEqual tag (constant 3) (eq C (listCons (tagged 2 .zero) .zero))
    (ifEqual tag (constant 4)
      (allOf [mem (listCons φ (listCons ψ Γ)), eq C (listCons (tagged 5 (.pair φ ψ)) Γ)])
    (ifEqual tag (constant 5)
      (allOf [mem (listCons φ Γ), mem (listCons ψ Γ), eq C (listCons (tagged 4 (.pair φ ψ)) Γ)])
    (ifEqual tag (constant 6)
      (allOf [mem (listCons (rwθ (constant 1)) (.comp proofRewriteSequent (.pair .zero Γ))),
        eq C (listCons (tagged 6 θ) Γ)])
    (ifEqual tag (constant 7)
      (allOf [mem (listCons (rwθ (.comp .succ (.comp .succ k))) Γ), eq C (listCons (tagged 7 θ) Γ)]) .zero)))))))

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def arithmeticLKRuleCore (S C tag φ ψ θ k Γ Δ : M) : Prop :=
  if tag = 0 then C = Arithmetic.pair φ (Arithmetic.pair (negateCode.evalArithmetic φ) 0 + 1) + 1 else
  if tag = 1 then
    listMember.evalArithmetic (Arithmetic.pair (Arithmetic.pair φ Γ + 1) S) = 1 ∧
    listMember.evalArithmetic (Arithmetic.pair (Arithmetic.pair (negateCode.evalArithmetic φ) Δ + 1) S) = 1 ∧
    C = listAppend.evalArithmetic (Arithmetic.pair Δ Γ) else
  if tag = 2 then listMember.evalArithmetic (Arithmetic.pair Δ S) = 1 ∧
    listSubset.evalArithmetic (Arithmetic.pair Δ C) = 1 else
  if tag = 3 then C = Arithmetic.pair (Arithmetic.pair 2 0 + 1) 0 + 1 else
  if tag = 4 then
    listMember.evalArithmetic (Arithmetic.pair (Arithmetic.pair φ (Arithmetic.pair ψ Γ + 1) + 1) S) = 1 ∧
    C = Arithmetic.pair (Arithmetic.pair 5 (Arithmetic.pair φ ψ) + 1) Γ + 1 else
  if tag = 5 then
    listMember.evalArithmetic (Arithmetic.pair (Arithmetic.pair φ Γ + 1) S) = 1 ∧
    listMember.evalArithmetic (Arithmetic.pair (Arithmetic.pair ψ Γ + 1) S) = 1 ∧
    C = Arithmetic.pair (Arithmetic.pair 4 (Arithmetic.pair φ ψ) + 1) Γ + 1 else
  if tag = 6 then
    listMember.evalArithmetic (Arithmetic.pair (Arithmetic.pair
      (proofRewriteCode.evalArithmetic (Arithmetic.pair 1 (Arithmetic.pair 0 θ)))
      (proofRewriteSequent.evalArithmetic (Arithmetic.pair 0 Γ)) + 1) S) = 1 ∧
    C = Arithmetic.pair (Arithmetic.pair 6 θ + 1) Γ + 1 else
  if tag = 7 then
    listMember.evalArithmetic (Arithmetic.pair (Arithmetic.pair
      (proofRewriteCode.evalArithmetic (Arithmetic.pair (k + 1 + 1) (Arithmetic.pair 0 θ))) Γ + 1) S) = 1 ∧
    C = Arithmetic.pair (Arithmetic.pair 7 θ + 1) Γ + 1 else False

theorem evalArithmetic_lkRuleCore_ne_zero (S C tag φ ψ θ k Γ Δ : M) :
    lkRuleCore.evalArithmetic (Arithmetic.pair S (Arithmetic.pair C (Arithmetic.pair tag
      (Arithmetic.pair φ (Arithmetic.pair ψ (Arithmetic.pair θ (Arithmetic.pair k (Arithmetic.pair Γ Δ)))))))) ≠ 0 ↔
      arithmeticLKRuleCore S C tag φ ψ θ k Γ Δ := by
  by_cases h0 : tag = 0
  · simp [lkRuleCore, arithmeticLKRuleCore, listCons, h0, -evalArithmetic_proofRewriteCode]
  by_cases h1 : tag = 1
  · simp [lkRuleCore, arithmeticLKRuleCore, listCons, h1, -evalArithmetic_proofRewriteCode]
  by_cases h2 : tag = 2
  · simp [lkRuleCore, arithmeticLKRuleCore, listCons, h2, -evalArithmetic_proofRewriteCode]
  by_cases h3 : tag = 3
  · simp [lkRuleCore, arithmeticLKRuleCore, listCons, h3, -evalArithmetic_proofRewriteCode]
  by_cases h4 : tag = 4
  · simp [lkRuleCore, arithmeticLKRuleCore, listCons, h4, -evalArithmetic_proofRewriteCode]
  by_cases h5 : tag = 5
  · simp [lkRuleCore, arithmeticLKRuleCore, listCons, h5, -evalArithmetic_proofRewriteCode]
  by_cases h6 : tag = 6
  · simp [lkRuleCore, arithmeticLKRuleCore, listCons, h6, -evalArithmetic_proofRewriteCode]
  by_cases h7 : tag = 7
  · simp [lkRuleCore, arithmeticLKRuleCore, listCons, h7, -evalArithmetic_proofRewriteCode]
  · simp [lkRuleCore, arithmeticLKRuleCore, listCons, h0, h1, h2, h3, h4, h5, h6, h7, -evalArithmetic_proofRewriteCode]

end PrimitiveProgram
end ZFVP
