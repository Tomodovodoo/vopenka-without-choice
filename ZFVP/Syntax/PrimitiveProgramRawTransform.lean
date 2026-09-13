import ZFVP.Syntax.RawFormulaCoding
import ZFVP.Syntax.PrimitiveProgramFormulaTransformEquations
import ZFVP.Syntax.PrimitiveProgramNegationStandard

/-! Raw truth and falsity payloads do not affect explicit formula transformations. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

theorem RawFormulaCode.formulaTransform {ξ : Type*} [Encodable ξ] {n c : ℕ}
    {φ : Semiformula ℒₛₑₜ ξ n} (h : RawFormulaCode c φ) (arguments : PrimitiveProgram) (s d : ℕ) :
    (formulaTransformCode arguments).eval (Nat.pair s (Nat.pair d c)) =
      (formulaTransformCode arguments).eval (Nat.pair s (Nat.pair d (Encodable.encode φ))) := by
  rw [← evalArithmetic_nat, ← evalArithmetic_nat]
  induction h generalizing d with
  | rel r ts => rfl
  | nrel r ts => rfl
  | verum a =>
    have he (x : ℕ) := evalArithmetic_formulaTransformCode_verum arguments (s : ℕ) d x
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat] at he
    change (formulaTransformCode arguments).evalArithmetic (Nat.pair s (Nat.pair d (Nat.pair 2 a + 1))) =
      (formulaTransformCode arguments).evalArithmetic (Nat.pair s (Nat.pair d (Nat.pair 2 0 + 1)))
    rw [he, he]
  | falsum a =>
    have he (x : ℕ) := evalArithmetic_formulaTransformCode_falsum arguments (s : ℕ) d x
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat] at he
    change (formulaTransformCode arguments).evalArithmetic (Nat.pair s (Nat.pair d (Nat.pair 3 a + 1))) =
      (formulaTransformCode arguments).evalArithmetic (Nat.pair s (Nat.pair d (Nat.pair 3 0 + 1)))
    rw [he, he]
  | @and n a b φ ψ ha hb iha ihb =>
    have he (x y : ℕ) := evalArithmetic_formulaTransformCode_and arguments (s : ℕ) d x y
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat] at he
    change (formulaTransformCode arguments).evalArithmetic (Nat.pair s (Nat.pair d (Nat.pair 4 (Nat.pair a b) + 1))) =
      (formulaTransformCode arguments).evalArithmetic
        (Nat.pair s (Nat.pair d (Nat.pair 4 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1)))
    rw [he, he, iha, ihb]
  | @or n a b φ ψ ha hb iha ihb =>
    have he (x y : ℕ) := evalArithmetic_formulaTransformCode_or arguments (s : ℕ) d x y
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat] at he
    change (formulaTransformCode arguments).evalArithmetic (Nat.pair s (Nat.pair d (Nat.pair 5 (Nat.pair a b) + 1))) =
      (formulaTransformCode arguments).evalArithmetic
        (Nat.pair s (Nat.pair d (Nat.pair 5 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1)))
    rw [he, he, iha, ihb]
  | @all n a φ ha ih =>
    have he (x : ℕ) := evalArithmetic_formulaTransformCode_all arguments (s : ℕ) d x
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat] at he
    change (formulaTransformCode arguments).evalArithmetic (Nat.pair s (Nat.pair d (Nat.pair 6 a + 1))) =
      (formulaTransformCode arguments).evalArithmetic (Nat.pair s (Nat.pair d (Nat.pair 6 (Encodable.encode φ) + 1)))
    rw [he, he, ih]
  | @exs n a φ ha ih =>
    have he (x : ℕ) := evalArithmetic_formulaTransformCode_exs arguments (s : ℕ) d x
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat] at he
    change (formulaTransformCode arguments).evalArithmetic (Nat.pair s (Nat.pair d (Nat.pair 7 a + 1))) =
      (formulaTransformCode arguments).evalArithmetic (Nat.pair s (Nat.pair d (Nat.pair 7 (Encodable.encode φ) + 1)))
    rw [he, he, ih]

theorem RawFormulaCode.negate_program {ξ : Type*} [Encodable ξ] {n c : ℕ}
    {φ : Semiformula ℒₛₑₜ ξ n} (h : RawFormulaCode c φ) :
    negateCode.eval c = Encodable.encode (∼φ) := by
  rw [← evalArithmetic_nat]
  induction h with
  | rel r ts => exact (evalArithmetic_nat _ _).trans (negateCode_encode _)
  | nrel r ts => exact (evalArithmetic_nat _ _).trans (negateCode_encode _)
  | verum a =>
    change negateCode.evalArithmetic (Nat.pair 2 a + 1) = Nat.pair 3 0 + 1
    simpa only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat]
      using evalArithmetic_negateCode_verum (a : ℕ)
  | falsum a =>
    change negateCode.evalArithmetic (Nat.pair 3 a + 1) = Nat.pair 2 0 + 1
    simpa only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat]
      using evalArithmetic_negateCode_falsum (a : ℕ)
  | @and n a b φ ψ ha hb iha ihb =>
    change negateCode.evalArithmetic (Nat.pair 4 (Nat.pair a b) + 1) =
      Nat.pair 5 (Nat.pair (Encodable.encode (∼φ)) (Encodable.encode (∼ψ))) + 1
    simpa only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat, iha, ihb]
      using evalArithmetic_negateCode_and (a : ℕ) b
  | @or n a b φ ψ ha hb iha ihb =>
    change negateCode.evalArithmetic (Nat.pair 5 (Nat.pair a b) + 1) =
      Nat.pair 4 (Nat.pair (Encodable.encode (∼φ)) (Encodable.encode (∼ψ))) + 1
    simpa only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat, iha, ihb]
      using evalArithmetic_negateCode_or (a : ℕ) b
  | @all n a φ ha ih =>
    change negateCode.evalArithmetic (Nat.pair 6 a + 1) = Nat.pair 7 (Encodable.encode (∼φ)) + 1
    simpa only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat, ih]
      using evalArithmetic_negateCode_all (a : ℕ)
  | @exs n a φ ha ih =>
    change negateCode.evalArithmetic (Nat.pair 7 a + 1) = Nat.pair 6 (Encodable.encode (∼φ)) + 1
    simpa only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat, ih]
      using evalArithmetic_negateCode_exs (a : ℕ)

end ZFVP
