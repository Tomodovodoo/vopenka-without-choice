import ZFVP.Syntax.PrimitiveProgramNegation
import ZFVP.Syntax.NaturalFormulaNegation

/-! The explicit negation program implements negation of the standard membership syntax. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace PrimitiveProgram

theorem negateCode_encode {ξ : Type*} [Encodable ξ] {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n) :
    negateCode.eval (Encodable.encode φ) = Encodable.encode (∼φ) := by
  rw [← evalArithmetic_nat]
  induction φ with
  | verum =>
    change negateCode.evalArithmetic (Nat.pair 2 0 + 1) = Nat.pair 3 0 + 1
    simpa only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat] using evalArithmetic_negateCode_verum (0 : ℕ)
  | falsum =>
    change negateCode.evalArithmetic (Nat.pair 3 0 + 1) = Nat.pair 2 0 + 1
    simpa only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat] using evalArithmetic_negateCode_falsum (0 : ℕ)
  | rel r ts =>
    simp [Semiformula.encode_rel, Semiformula.encode_nrel, ← arithmeticPair_nat]
  | nrel r ts =>
    simp [Semiformula.encode_rel, Semiformula.encode_nrel, ← arithmeticPair_nat]
  | and φ ψ ihφ ihψ =>
    change negateCode.evalArithmetic (Nat.pair 4 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1) =
      Nat.pair 5 (Nat.pair (Encodable.encode (∼φ)) (Encodable.encode (∼ψ))) + 1
    simpa only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat, ihφ, ihψ] using evalArithmetic_negateCode_and (Encodable.encode φ) (Encodable.encode ψ)
  | or φ ψ ihφ ihψ =>
    change negateCode.evalArithmetic (Nat.pair 5 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1) =
      Nat.pair 4 (Nat.pair (Encodable.encode (∼φ)) (Encodable.encode (∼ψ))) + 1
    simpa only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat, ihφ, ihψ] using evalArithmetic_negateCode_or (Encodable.encode φ) (Encodable.encode ψ)
  | all φ ih =>
    change negateCode.evalArithmetic (Nat.pair 6 (Encodable.encode φ) + 1) = Nat.pair 7 (Encodable.encode (∼φ)) + 1
    simpa only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat, ih] using evalArithmetic_negateCode_all (Encodable.encode φ)
  | exs φ ih =>
    change negateCode.evalArithmetic (Nat.pair 7 (Encodable.encode φ) + 1) = Nat.pair 6 (Encodable.encode (∼φ)) + 1
    simpa only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat, ih] using evalArithmetic_negateCode_exs (Encodable.encode φ)

theorem negateCode_agrees_on_formula {ξ : Type*} [Encodable ξ] {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n) :
    negateCode.eval (Encodable.encode φ) = negateNatFormula (Encodable.encode φ) := by
  rw [negateCode_encode, negateNatFormula_encode]

end PrimitiveProgram
end ZFVP
