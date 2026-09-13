import ZFVP.Syntax.PrimitiveProgramLKStandardRule
import ZFVP.Syntax.NaturalLKCompleteness

/-! Exact standard-certificate correspondence for the explicit LK proof checker. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace PrimitiveProgram

theorem lkCertificateRun_encode_left (z : ℕ) (p : LKCertificateData) :
    (Nat.unpair (PrimitiveProgram.lkCertificateRun.eval (Nat.pair z (Encodable.encode p)))).1 =
      Encodable.encode (p.map Prod.fst) := by
  induction p with
  | nil =>
    have h := evalArithmetic_lkCertificateRun_zero (z : ℕ)
    simp only [arithmeticPair_nat, evalArithmetic_nat] at h
    change (Nat.unpair (PrimitiveProgram.lkCertificateRun.eval (Nat.pair z 0))).1 = 0
    rw [h, Nat.unpair_pair]
  | cons row p ih =>
    obtain ⟨C, w⟩ := row
    have h := evalArithmetic_lkCertificateRun_cons_left (z : ℕ)
      (Encodable.encode C : ℕ) (Encodable.encode w : ℕ) (Encodable.encode p : ℕ)
    simp only [arithmeticPiOne_nat, arithmeticPair_nat, evalArithmetic_nat] at h
    simp only [List.map_cons, Encodable.encode_list_cons, Encodable.encode_prod_val, Nat.succ_eq_add_one]
    rw [h, ih]

theorem lkCertificateRun_encode_right_eq_one (z : ℕ) (p : LKCertificateData) :
    (Nat.unpair (PrimitiveProgram.lkCertificateRun.eval (Nat.pair z (Encodable.encode p)))).2 = 1 ↔
      LKCertificate p := by
  induction p with
  | nil =>
    have h := evalArithmetic_lkCertificateRun_zero (z : ℕ)
    simp only [arithmeticPair_nat, evalArithmetic_nat] at h
    change (Nat.unpair (PrimitiveProgram.lkCertificateRun.eval (Nat.pair z 0))).2 = 1 ↔ True
    rw [h, Nat.unpair_pair]
    exact iff_true_intro rfl
  | cons row p ih =>
    obtain ⟨C, w⟩ := row
    have h := evalArithmetic_lkCertificateRun_cons_right_eq_one (z : ℕ)
      (Encodable.encode C : ℕ) (Encodable.encode w : ℕ) (Encodable.encode p : ℕ)
    simp only [arithmeticPiOne_nat, arithmeticPiTwo_nat, arithmeticPair_nat, evalArithmetic_nat] at h
    rw [ih, lkCertificateRun_encode_left, lkRuleCheck_encode] at h
    simp only [Encodable.encode_list_cons, Encodable.encode_prod_val, Nat.succ_eq_add_one, LKCertificate]
    exact h.trans and_comm

theorem lkProofCheck_encode (C : Sequent ℒₛₑₜ) (p : LKCertificateData) :
    lkProofCheck.eval (Nat.pair (Encodable.encode C) (Encodable.encode p)) = 1 ↔
      LKProofCertificate C p := by
  rw [← evalArithmetic_nat, ← arithmeticPair_nat, evalArithmetic_lkProofCheck_eq_one]
  simp only [arithmeticPiOne_nat, arithmeticPiTwo_nat, arithmeticPair_nat, evalArithmetic_nat]
  rw [lkCertificateRun_encode_left, lkCertificateRun_encode_right_eq_one, listMember_encode]
  rfl

theorem exists_lkProofCheck_encode_iff (C : Sequent ℒₛₑₜ) :
    (∃ p : LKCertificateData, lkProofCheck.eval (Nat.pair (Encodable.encode C) (Encodable.encode p)) = 1) ↔
      Nonempty (Derivation C) := by
  simp only [lkProofCheck_encode]
  exact lkCertified_iff C

end PrimitiveProgram
end ZFVP
