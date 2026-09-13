import ZFVP.Syntax.PrimitiveProgramReindex
import ZFVP.Syntax.PrimitiveProgramProofRewriteStandard
import ZFVP.Syntax.TemplatePrimrec

/-! The explicit renaming program implements the standard capture-avoiding index renaming. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace PrimitiveProgram

theorem arithmeticReindexVariable_nat (r : List ℕ) (d i : ℕ) :
    arithmeticReindexVariable (Encodable.encode r : ℕ) d i = reindexNatVariable r d i := by
  unfold arithmeticReindexVariable reindexNatVariable
  simp only [arithmeticSubNotation_nat, evalArithmetic_listLength_encode]
  by_cases hi : i < d
  · simp only [hi, ite_true]
  · simp only [hi, ite_false]
    by_cases hj : i - d < r.length
    · rw [ite_eq_left hj, evalArithmetic_listGet_encode r _ hj]
      simp [List.getD_eq_getElem?_getD, hj]
    · rw [ite_eq_right hj]
      simp [List.getD_eq_getElem?_getD, hj]

theorem arithmeticReindexTerm_nat (r : List ℕ) (d c : ℕ) :
    arithmeticReindexTerm (Encodable.encode r : ℕ) d c = reindexNatTerm r d c := by
  unfold arithmeticReindexTerm reindexNatTerm
  simp only [arithmeticSubNotation_nat, arithmeticPiTwo_nat, arithmeticPair_nat,
    arithmeticReindexVariable_nat]

theorem reindexArguments_nat (r : List ℕ) (d c : ℕ) :
    reindexArguments.eval (Nat.pair (Encodable.encode r) (Nat.pair d c)) = reindexNatArguments r d c := by
  rw [← evalArithmetic_nat, ← arithmeticPair_nat, ← arithmeticPair_nat, evalArithmetic_reindexArguments]
  unfold reindexNatArguments natVectorTwo
  simp only [evalArithmetic_listHead, evalArithmetic_listTail, OfNat.ofNat, One.one, Zero.zero,
    arithmeticSubNotation_nat, arithmeticPiOne_nat, arithmeticPiTwo_nat, arithmeticPair_nat,
    arithmeticReindexTerm_nat]

theorem reindexCode_encode (s : List ℕ) (d : ℕ) {n : ℕ} (φ : SetTheorySemisentence n) :
    (formulaTransformCode reindexArguments).eval (Nat.pair (Encodable.encode s) (Nat.pair d (Encodable.encode φ))) =
      reindexNatFormula s d (Encodable.encode φ) := by
  induction φ generalizing d with
  | verum =>
    have he := evalArithmetic_formulaTransformCode_verum reindexArguments (M := ℕ) (Encodable.encode s) d 0
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat, evalArithmetic_nat] at he
    change (formulaTransformCode reindexArguments).eval (Nat.pair (Encodable.encode s) (Nat.pair d (Nat.pair 2 0 + 1))) = _
    rw [he]
    simp [Semiformula.encode_eq_toNat, Semiformula.toNat, reindexNatFormula]
  | falsum =>
    have he := evalArithmetic_formulaTransformCode_falsum reindexArguments (M := ℕ) (Encodable.encode s) d 0
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat, evalArithmetic_nat] at he
    change (formulaTransformCode reindexArguments).eval (Nat.pair (Encodable.encode s) (Nat.pair d (Nat.pair 3 0 + 1))) = _
    rw [he]
    simp [Semiformula.encode_eq_toNat, Semiformula.toNat, reindexNatFormula]
  | @rel n k r ts =>
    have he := evalArithmetic_formulaTransformCode_rel reindexArguments (M := ℕ) (Encodable.encode s) d
      (Nat.pair k (Nat.pair (Encodable.encode r) (Matrix.vecToNat (fun i ↦ Encodable.encode (ts i)))))
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Zero.zero, Arithmetic.natCast_nat,
      arithmeticPiOne_nat, arithmeticPiTwo_nat, Nat.unpair_pair, evalArithmetic_nat, reindexArguments_nat] at he
    rw [Semiformula.encode_rel, he]
    cases r <;> simp [reindexNatFormula]
  | @nrel n k r ts =>
    have he := evalArithmetic_formulaTransformCode_nrel reindexArguments (M := ℕ) (Encodable.encode s) d
      (Nat.pair k (Nat.pair (Encodable.encode r) (Matrix.vecToNat (fun i ↦ Encodable.encode (ts i)))))
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat,
      arithmeticPiOne_nat, arithmeticPiTwo_nat, Nat.unpair_pair, evalArithmetic_nat, reindexArguments_nat] at he
    rw [Semiformula.encode_nrel, he]
    cases r <;> simp [reindexNatFormula]
  | and φ ψ ihφ ihψ =>
    have he := evalArithmetic_formulaTransformCode_and reindexArguments (M := ℕ) (Encodable.encode s) d (Encodable.encode φ) (Encodable.encode ψ)
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat, evalArithmetic_nat] at he
    change (formulaTransformCode reindexArguments).eval (Nat.pair (Encodable.encode s) (Nat.pair d (Nat.pair 4 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1))) = _
    rw [he, ihφ, ihψ]
    simp [Semiformula.encode_eq_toNat, Semiformula.toNat, reindexNatFormula]
  | or φ ψ ihφ ihψ =>
    have he := evalArithmetic_formulaTransformCode_or reindexArguments (M := ℕ) (Encodable.encode s) d (Encodable.encode φ) (Encodable.encode ψ)
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat, evalArithmetic_nat] at he
    change (formulaTransformCode reindexArguments).eval (Nat.pair (Encodable.encode s) (Nat.pair d (Nat.pair 5 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1))) = _
    rw [he, ihφ, ihψ]
    simp [Semiformula.encode_eq_toNat, Semiformula.toNat, reindexNatFormula]
  | all φ ih =>
    have he := evalArithmetic_formulaTransformCode_all reindexArguments (M := ℕ) (Encodable.encode s) d (Encodable.encode φ)
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat, evalArithmetic_nat] at he
    change (formulaTransformCode reindexArguments).eval (Nat.pair (Encodable.encode s) (Nat.pair d (Nat.pair 6 (Encodable.encode φ) + 1))) = _
    rw [he, ih]
    simp [Semiformula.encode_eq_toNat, Semiformula.toNat, reindexNatFormula]
  | exs φ ih =>
    have he := evalArithmetic_formulaTransformCode_exs reindexArguments (M := ℕ) (Encodable.encode s) d (Encodable.encode φ)
    simp only [arithmeticPair_nat, OfNat.ofNat, One.one, Arithmetic.natCast_nat, evalArithmetic_nat] at he
    change (formulaTransformCode reindexArguments).eval (Nat.pair (Encodable.encode s) (Nat.pair d (Nat.pair 7 (Encodable.encode φ) + 1))) = _
    rw [he, ih]
    simp [Semiformula.encode_eq_toNat, Semiformula.toNat, reindexNatFormula]

theorem reindexCode_boundIndexRew_encode {n m : ℕ} (r : Fin n → Fin m) (φ : SetTheorySemisentence n) :
    reindexCode.eval (Nat.pair (Encodable.encode (List.ofFn (fun i ↦ (r i).val)))
      (Nat.pair 0 (Encodable.encode φ))) = Encodable.encode (boundIndexRew r ▹ φ) := by
  rw [reindexCode, reindexCode_encode, reindexNatFormula_boundIndexRew]

end PrimitiveProgram
end ZFVP
