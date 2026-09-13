import ZFVP.Syntax.PrimitiveProgramRawAtoms
import ZFVP.Syntax.PrimitiveProgramLKStandardInputs

/-! Accepted raw standard formula codes decode to well-formed typed formulas. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace PrimitiveProgram

theorem formulaRequirement_raw {ξ : Type*} [Encodable ξ] (allowFree : Bool)
    (hdec : ∀ i : ℕ, allowFree = true → ∃ x : ξ, Encodable.encode x = i) {c n : ℕ}
    (hv : (formulaRequirement allowFree).evalArithmetic c ≠ 0 ∧
      (formulaRequirement allowFree).evalArithmetic c ≤ n + 1) :
    ∃ φ : Semiformula ℒₛₑₜ ξ n, RawFormulaCode c φ := by
  classical
  induction c using Nat.strong_induction_on generalizing n with
  | h c ih =>
    cases c with
    | zero => simp at hv
    | succ c =>
      obtain ⟨t, a, rfl⟩ : ∃ t a, c = Nat.pair t a :=
        ⟨c.unpair.1, c.unpair.2, (Nat.pair_unpair c).symm⟩
      have ha : a < Nat.pair t a + 1 := Nat.lt_succ_of_le (Nat.right_le_pair t a)
      have hl := lt_of_le_of_lt (Nat.unpair_left_le a) ha
      have hr := lt_of_le_of_lt (Nat.unpair_right_le a) ha
      have he := evalArithmetic_formulaRequirement_tagged allowFree (t : ℕ) a
      simp only [arithmeticPair_nat] at he
      rw [he] at hv
      unfold formulaRequirementValue at hv
      split_ifs at hv with h0 h1 h2 h3 h4 h5 h6 h7
      · subst t
        obtain ⟨k, r, ts, rfl⟩ := atomicRequirement_raw allowFree hdec hv
        exact ⟨.rel r ts, .rel r ts⟩
      · subst t
        obtain ⟨k, r, ts, rfl⟩ := atomicRequirement_raw allowFree hdec hv
        exact ⟨.nrel r ts, .nrel r ts⟩
      · subst t
        exact ⟨⊤, .verum a⟩
      · subst t
        exact ⟨⊥, .falsum a⟩
      · subst t
        have hj := joinRequirements_valid_iff
          ((formulaRequirement allowFree).evalArithmetic (Arithmetic.pi₁ a))
          ((formulaRequirement allowFree).evalArithmetic (Arithmetic.pi₂ a)) (n + 1)
        simp only [arithmeticLE_nat] at hj
        obtain ⟨hvφ, hvψ⟩ := hj.mp hv
        simp only [arithmeticPiOne_nat, arithmeticPiTwo_nat] at hvφ hvψ
        obtain ⟨φ, hφ⟩ := ih a.unpair.1 hl hvφ
        obtain ⟨ψ, hψ⟩ := ih a.unpair.2 hr hvψ
        exact ⟨φ ⋏ ψ, by simpa only [Nat.pair_unpair, OfNat.ofNat, One.one, Arithmetic.natCast_nat] using RawFormulaCode.and hφ hψ⟩
      · subst t
        have hj := joinRequirements_valid_iff
          ((formulaRequirement allowFree).evalArithmetic (Arithmetic.pi₁ a))
          ((formulaRequirement allowFree).evalArithmetic (Arithmetic.pi₂ a)) (n + 1)
        simp only [arithmeticLE_nat] at hj
        obtain ⟨hvφ, hvψ⟩ := hj.mp hv
        simp only [arithmeticPiOne_nat, arithmeticPiTwo_nat] at hvφ hvψ
        obtain ⟨φ, hφ⟩ := ih a.unpair.1 hl hvφ
        obtain ⟨ψ, hψ⟩ := ih a.unpair.2 hr hvψ
        exact ⟨φ ⋎ ψ, by simpa only [Nat.pair_unpair, OfNat.ofNat, One.one, Arithmetic.natCast_nat] using RawFormulaCode.or hφ hψ⟩
      · subst t
        have hq := quantifyRequirement_valid_iff ((formulaRequirement allowFree).evalArithmetic a) n
        simp only [arithmeticLE_nat] at hq
        obtain ⟨φ, hφ⟩ := ih a ha (hq.mp hv)
        exact ⟨∀¹ φ, .all hφ⟩
      · subst t
        have hq := quantifyRequirement_valid_iff ((formulaRequirement allowFree).evalArithmetic a) n
        simp only [arithmeticLE_nat] at hq
        obtain ⟨φ, hφ⟩ := ih a ha (hq.mp hv)
        exact ⟨∃¹ φ, .exs hφ⟩
      · exact (hv.1 rfl).elim

theorem formulaCheck_raw_closed {n c : ℕ}
    (hv : (formulaCheck false).eval (Nat.pair n c) = 1) :
    ∃ φ : SetTheorySemisentence n, RawFormulaCode c φ := by
  rw [← evalArithmetic_nat, ← arithmeticPair_nat, evalArithmetic_formulaCheck_eq_one, arithmeticLE_nat] at hv
  exact formulaRequirement_raw false (fun _ h ↦ Bool.noConfusion h) hv

theorem formulaCheck_raw_open {n c : ℕ}
    (hv : (formulaCheck true).eval (Nat.pair n c) = 1) :
    ∃ φ : Semiproposition ℒₛₑₜ n, RawFormulaCode c φ := by
  rw [← evalArithmetic_nat, ← arithmeticPair_nat, evalArithmetic_formulaCheck_eq_one, arithmeticLE_nat] at hv
  exact formulaRequirement_raw true (fun i _ ↦ ⟨i, rfl⟩) hv

end PrimitiveProgram
end ZFVP
