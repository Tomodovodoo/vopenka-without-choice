import ZFVP.Syntax.RawSequentCoding

/-! Standard decoding commutes with the formula operations used by the LK rule checker. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

theorem rawFormula_negate {n c : ℕ} (hv : (formulaCheck true).eval (Nat.pair n c) = 1) :
    rawFormula n (negateCode.eval c) = ∼rawFormula n c := by
  rw [(rawFormula_code hv).negate_program, rawFormula_encode]

theorem rawFormula_and {n a b : ℕ} (ha : (formulaCheck true).eval (Nat.pair n a) = 1)
    (hb : (formulaCheck true).eval (Nat.pair n b) = 1) :
    rawFormula n (Nat.pair 4 (Nat.pair a b) + 1) = rawFormula n a ⋏ rawFormula n b :=
  (RawFormulaCode.and (rawFormula_code ha) (rawFormula_code hb)).decode_raw

theorem rawFormula_or {n a b : ℕ} (ha : (formulaCheck true).eval (Nat.pair n a) = 1)
    (hb : (formulaCheck true).eval (Nat.pair n b) = 1) :
    rawFormula n (Nat.pair 5 (Nat.pair a b) + 1) = rawFormula n a ⋎ rawFormula n b :=
  (RawFormulaCode.or (rawFormula_code ha) (rawFormula_code hb)).decode_raw

theorem rawFormula_all {n c : ℕ} (hv : (formulaCheck true).eval (Nat.pair (n + 1) c) = 1) :
    rawFormula n (Nat.pair 6 c + 1) = ∀¹ (rawFormula (n + 1) c) :=
  (RawFormulaCode.all (rawFormula_code hv)).decode_raw

theorem rawFormula_exs {n c : ℕ} (hv : (formulaCheck true).eval (Nat.pair (n + 1) c) = 1) :
    rawFormula n (Nat.pair 7 c + 1) = ∃¹ (rawFormula (n + 1) c) :=
  (RawFormulaCode.exs (rawFormula_code hv)).decode_raw

theorem proofRewriteAtZero_raw {n c : ℕ} {φ : Semiproposition ℒₛₑₜ n}
    (hφ : RawFormulaCode c φ) (s : ℕ) :
    proofRewriteAtZero.eval (Nat.pair s c) = proofRewriteAtZero.eval (Nat.pair s (Encodable.encode φ)) := by
  have he (x : ℕ) := evalArithmetic_proofRewriteAtZero (s : ℕ) x
  simp only [arithmeticPair_nat, evalArithmetic_nat] at he
  rw [he, he]
  exact hφ.formulaTransform proofRewriteArguments s 0

theorem rawFormula_shift {c : ℕ} (hv : (formulaCheck true).eval (Nat.pair 0 c) = 1) :
    rawFormula 0 (proofRewriteAtZero.eval (Nat.pair 0 c)) = (rawFormula 0 c).shift := by
  rw [proofRewriteAtZero_raw (rawFormula_code hv), proofRewriteAtZero_shift_encode, rawFormula_encode]

theorem rawFormula_free {c : ℕ} (hv : (formulaCheck true).eval (Nat.pair 1 c) = 1) :
    rawFormula 0 (proofRewriteAtZero.eval (Nat.pair 1 c)) = (rawFormula 1 c).free := by
  rw [proofRewriteAtZero_raw (rawFormula_code hv), proofRewriteAtZero_free_encode, rawFormula_encode]

theorem rawFormula_subst {c : ℕ} (k : ℕ) (hv : (formulaCheck true).eval (Nat.pair 1 c) = 1) :
    rawFormula 0 (proofRewriteAtZero.eval (Nat.pair (k + 2) c)) = (rawFormula 1 c)/[&k] := by
  rw [proofRewriteAtZero_raw (rawFormula_code hv), proofRewriteAtZero_subst_encode, rawFormula_encode]

theorem rawSequent_shift {cs : ℕ} (hv : (sequentCheck true).eval (Nat.pair 0 cs) = 1) :
    rawSequent (proofRewriteSequent.eval (Nat.pair 0 cs)) = (rawSequent cs).map Semiformula.shift := by
  rw [proofRewriteSequent, rawSequent_listMap]
  simp only [rawSequent, List.map_map]
  apply List.map_congr_left
  intro c hc
  exact rawFormula_shift ((sequentCheck_natToList true 0 cs).mp hv c hc)

end ZFVP
