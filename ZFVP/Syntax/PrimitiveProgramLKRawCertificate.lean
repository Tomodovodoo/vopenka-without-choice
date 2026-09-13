import ZFVP.Syntax.PrimitiveProgramLKRawRule
import ZFVP.Syntax.PrimitiveProgramLKStandardCertificate

/-! Every accepted raw standard LK certificate reconstructs a Foundation derivation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

private theorem natToList_cons (a b : ℕ) :
    Nat.natToList (Nat.pair a b + 1) = a :: Nat.natToList b := by
  simp [Nat.natToList]

theorem lkCertificateRun_raw_sound (z p : ℕ)
    (hcheck : (Nat.unpair (PrimitiveProgram.lkCertificateRun.eval (Nat.pair z p))).2 = 1) :
    ∀ c ∈ Nat.natToList (Nat.unpair (PrimitiveProgram.lkCertificateRun.eval (Nat.pair z p))).1,
      Nonempty (Derivation (rawSequent c)) := by
  have H (rows : List ℕ) :
      (Nat.unpair (PrimitiveProgram.lkCertificateRun.eval (Nat.pair z (Encodable.encode rows)))).2 = 1 →
      ∀ c ∈ Nat.natToList (Nat.unpair (PrimitiveProgram.lkCertificateRun.eval (Nat.pair z (Encodable.encode rows)))).1,
        Nonempty (Derivation (rawSequent c)) := by
    induction rows with
    | nil =>
      intro _ c hc
      have he := evalArithmetic_lkCertificateRun_zero (z : ℕ)
      simp only [arithmeticPair_nat, evalArithmetic_nat, OfNat.ofNat, One.one, Zero.zero] at he
      simp only [Encodable.encode_list_nil, he, Nat.unpair_pair, Nat.natToList, List.not_mem_nil] at hc
    | cons row rows ih =>
      obtain ⟨C, w, rfl⟩ := rawPair_cases row
      intro hcheck c hc
      have he := evalArithmetic_lkCertificateRun_cons_right_eq_one (z : ℕ) C w (Encodable.encode rows)
      have hleft := evalArithmetic_lkCertificateRun_cons_left (z : ℕ) C w (Encodable.encode rows)
      simp only [arithmeticPair_nat, evalArithmetic_nat, arithmeticPiOne_nat, arithmeticPiTwo_nat,
        OfNat.ofNat, One.one] at he hleft
      simp only [Encodable.encode_list_cons, Encodable.encode_nat, Nat.succ_eq_add_one] at hcheck hc
      obtain ⟨hprev, hrule⟩ := he.mp hcheck
      rw [hleft, natToList_cons, List.mem_cons] at hc
      rcases hc with hc | hc
      · rw [hc]
        exact lkRuleCheck_raw_sound _ C w hrule (ih hprev)
      · exact ih hprev c hc
  have hp := H (Nat.natToList p)
  rw [encode_natToList] at hp
  exact hp hcheck

theorem lkProofCheck_raw_sound (C p : ℕ) (hcheck : lkProofCheck.eval (Nat.pair C p) = 1) :
    Nonempty (Derivation (rawSequent C)) := by
  have he := evalArithmetic_lkProofCheck_eq_one (C : ℕ) p
  simp only [arithmeticPair_nat, evalArithmetic_nat, arithmeticPiOne_nat, arithmeticPiTwo_nat] at he
  obtain ⟨hacc, hmem⟩ := he.mp hcheck
  exact lkCertificateRun_raw_sound 0 p hacc C ((listMember_natToList _ _).mp hmem)

theorem exists_lkProofCheck_iff (C : Sequent ℒₛₑₜ) :
    (∃ p : ℕ, lkProofCheck.eval (Nat.pair (Encodable.encode C) p) = 1) ↔ Nonempty (Derivation C) := by
  constructor
  · rintro ⟨p, hp⟩
    simpa only [rawSequent_encode] using lkProofCheck_raw_sound (Encodable.encode C) p hp
  · intro h
    obtain ⟨p, hp⟩ := (exists_lkProofCheck_encode_iff C).mpr h
    exact ⟨Encodable.encode p, hp⟩

end ZFVP
