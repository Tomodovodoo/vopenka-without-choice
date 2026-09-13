import ZFVP.Syntax.PrimitiveProgramForwardTabulate
import ZFVP.Syntax.PrimitiveProgramClosure
import ZFVP.Syntax.PrimitiveProgramListStandard
import ZFVP.Syntax.PrimitiveProgramNativeEquations

/-! Standard encodings of generated index tables and universal formula closure. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace PrimitiveProgram

theorem forwardTabulate_encode (f : PrimitiveProgram) (z n : ℕ) :
    (forwardTabulate f).eval (Nat.pair z n) = Encodable.encode ((List.range n).map (fun i ↦ f.eval (Nat.pair z i))) := by
  induction n with
  | zero =>
    rw [← evalArithmetic_nat, ← arithmeticPair_nat, evalArithmetic_forwardTabulate_zero]
    rfl
  | succ n ih =>
    have h := evalArithmetic_forwardTabulate_succ f (z : ℕ) n
    simp only [arithmeticPair_nat, evalArithmetic_nat] at h
    rw [h, ih]
    change listAppend.eval (Nat.pair (Encodable.encode [f.eval (Nat.pair z n)])
      (Encodable.encode ((List.range n).map (fun i ↦ f.eval (Nat.pair z i))))) = _
    rw [listAppend_encode, List.range_succ, List.map_append]
    rfl

theorem universalClosure_nat (k c : ℕ) :
    universalClosure.eval (Nat.pair k c) = allNatFormula k c := by
  induction k with
  | zero =>
    rw [← evalArithmetic_nat, ← arithmeticPair_nat, evalArithmetic_universalClosure_zero]
    rfl
  | succ k ih =>
    have h := evalArithmetic_universalClosure_succ (k : ℕ) c
    simp only [arithmeticPair_nat, evalArithmetic_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat] at h
    rw [h, ih]
    exact (Function.iterate_succ_apply' (fun c : ℕ ↦ Nat.pair 6 c + 1) k c).symm

theorem universalClosure_encode {n : ℕ} (φ : SetTheorySemisentence n) :
    universalClosure.eval (Nat.pair n (Encodable.encode φ)) = Encodable.encode (∀¹* φ) := by
  rw [universalClosure_nat, allNatFormula_encode]

end PrimitiveProgram
end ZFVP
