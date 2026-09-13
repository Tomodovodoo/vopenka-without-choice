import ZFVP.Syntax.PrimitiveProgramLKStandardInputs

/-! The explicit LK checker agrees with the standard typed rule witness format. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace PrimitiveProgram

theorem arithmeticLKRuleCore_encode (S : List (Sequent ℒₛₑₜ)) (C : Sequent ℒₛₑₜ)
    (tag : ℕ) (φ ψ : SetTheoryProposition) (θ : Semiproposition ℒₛₑₜ 1) (k : ℕ) (Γ Δ : Sequent ℒₛₑₜ) :
    arithmeticLKRuleCore (Encodable.encode S : ℕ) (Encodable.encode C : ℕ) tag
      (Encodable.encode φ : ℕ) (Encodable.encode ψ : ℕ) (Encodable.encode θ : ℕ) k
      (Encodable.encode Γ : ℕ) (Encodable.encode Δ : ℕ) ↔
      LKRuleCheck S C (tag, φ, ψ, θ, k, Γ, Δ) := by
  match tag with
  | 0 =>
    simp only [arithmeticLKRuleCore, ite_true, arithmeticPair_nat, evalArithmetic_nat, negateCode_encode]
    change Encodable.encode C = Encodable.encode [φ, ∼φ] ↔ C = [φ, ∼φ]
    exact Encodable.encode_injective.eq_iff
  | 1 =>
    norm_num only [arithmeticLKRuleCore, Zero.zero, One.one, ite_true, ite_false, arithmeticPair_nat,
      evalArithmetic_nat, negateCode_encode]
    change (listMember.eval (Nat.pair (Encodable.encode (φ :: Γ)) (Encodable.encode S)) = 1 ∧
      listMember.eval (Nat.pair (Encodable.encode (∼φ :: Δ)) (Encodable.encode S)) = 1 ∧
      Encodable.encode C = listAppend.eval (Nat.pair (Encodable.encode Δ) (Encodable.encode Γ))) ↔ _
    rw [listMember_encode, listMember_encode, listAppend_encode, Encodable.encode_injective.eq_iff]
    rfl
  | 2 =>
    norm_num only [arithmeticLKRuleCore, OfNat.ofNat, Zero.zero, One.one, Arithmetic.natCast_nat, ite_true, ite_false,
      arithmeticPair_nat, evalArithmetic_nat]
    rw [listMember_encode, listSubset_encode]
    rfl
  | 3 =>
    norm_num only [arithmeticLKRuleCore, OfNat.ofNat, Zero.zero, One.one, Arithmetic.natCast_nat, ite_true, ite_false,
      arithmeticPair_nat]
    change Encodable.encode C = Encodable.encode [(⊤ : SetTheoryProposition)] ↔ C = [⊤]
    exact Encodable.encode_injective.eq_iff
  | 4 =>
    norm_num only [arithmeticLKRuleCore, OfNat.ofNat, Zero.zero, One.one, Arithmetic.natCast_nat, ite_true, ite_false,
      arithmeticPair_nat, evalArithmetic_nat]
    change (listMember.eval (Nat.pair (Encodable.encode (φ :: ψ :: Γ)) (Encodable.encode S)) = 1 ∧
      Encodable.encode C = Encodable.encode ((φ ⋎ ψ) :: Γ)) ↔ _
    rw [listMember_encode, Encodable.encode_injective.eq_iff]
    rfl
  | 5 =>
    norm_num only [arithmeticLKRuleCore, OfNat.ofNat, Zero.zero, One.one, Arithmetic.natCast_nat, ite_true, ite_false,
      arithmeticPair_nat, evalArithmetic_nat]
    change (listMember.eval (Nat.pair (Encodable.encode (φ :: Γ)) (Encodable.encode S)) = 1 ∧
      listMember.eval (Nat.pair (Encodable.encode (ψ :: Γ)) (Encodable.encode S)) = 1 ∧
      Encodable.encode C = Encodable.encode ((φ ⋏ ψ) :: Γ)) ↔ _
    rw [listMember_encode, listMember_encode, Encodable.encode_injective.eq_iff]
    rfl
  | 6 =>
    norm_num only [arithmeticLKRuleCore, OfNat.ofNat, Zero.zero, One.one, Arithmetic.natCast_nat, ite_true, ite_false,
      arithmeticPair_nat, evalArithmetic_nat, proofRewriteCode_encode, proofRewNatFormula_free,
      proofRewriteSequent_shift_encode]
    change (listMember.eval (Nat.pair (Encodable.encode (θ.free :: Γ.map Semiformula.shift)) (Encodable.encode S)) = 1 ∧
      Encodable.encode C = Encodable.encode ((∀¹ θ) :: Γ)) ↔ _
    rw [listMember_encode, Encodable.encode_injective.eq_iff]
    rfl
  | 7 =>
    norm_num only [arithmeticLKRuleCore, OfNat.ofNat, Zero.zero, One.one, Arithmetic.natCast_nat, ite_true, ite_false,
      arithmeticPair_nat, evalArithmetic_nat, Nat.add_assoc, Nat.reduceAdd,
      proofRewriteCode_encode, proofRewNatFormula_subst]
    change (listMember.eval (Nat.pair (Encodable.encode (θ/[&k] :: Γ)) (Encodable.encode S)) = 1 ∧
      Encodable.encode C = Encodable.encode ((∃¹ θ) :: Γ)) ↔ _
    rw [listMember_encode, Encodable.encode_injective.eq_iff]
    rfl
  | n + 8 =>
    have h0 : n + 8 ≠ 0 := by omega
    have h1 : n + 8 ≠ 1 := by omega
    have h2 : n + 8 ≠ 2 := by omega
    have h3 : n + 8 ≠ 3 := by omega
    have h4 : n + 8 ≠ 4 := by omega
    have h5 : n + 8 ≠ 5 := by omega
    have h6 : n + 8 ≠ 6 := by omega
    have h7 : n + 8 ≠ 7 := by omega
    simp only [arithmeticLKRuleCore, OfNat.ofNat, Zero.zero, One.one, Arithmetic.natCast_nat, h0, h1, h2, h3, h4, h5, h6, h7,
      ite_false, LKRuleCheck]

theorem lkRuleCheck_encode (S : List (Sequent ℒₛₑₜ)) (C : Sequent ℒₛₑₜ) (w : LKRuleWitness) :
    lkRuleCheck.eval (Nat.pair (Encodable.encode S) (Nat.pair (Encodable.encode C) (Encodable.encode w))) = 1 ↔
      LKRuleCheck S C w := by
  obtain ⟨tag, φ, ψ, θ, k, Γ, Δ⟩ := w
  have h := evalArithmetic_lkRuleCheck_eq_one (Encodable.encode S : ℕ) (Encodable.encode C : ℕ) tag
    (Encodable.encode φ : ℕ) (Encodable.encode ψ : ℕ) (Encodable.encode θ : ℕ) k
    (Encodable.encode Γ : ℕ) (Encodable.encode Δ : ℕ)
  rw [arithmeticLKRuleCore_encode, and_iff_right (arithmeticLKInputs_encode S C φ ψ θ Γ Δ)] at h
  simpa only [arithmeticPair_nat, evalArithmetic_nat, Encodable.encode_prod_val, Encodable.encode_nat] using h

end PrimitiveProgram
end ZFVP
