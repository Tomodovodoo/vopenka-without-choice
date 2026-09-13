import ZFVP.Syntax.RawSequentOperations
import ZFVP.Syntax.PrimitiveProgramLKRuleCheck
import ZFVP.Syntax.NaturalLKRule

/-! Every accepted raw standard LK instruction yields a Foundation derivation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

theorem rawPair_cases (c : ℕ) : ∃ a b, c = Nat.pair a b :=
  ⟨c.unpair.1, c.unpair.2, (Nat.pair_unpair c).symm⟩

theorem arithmeticLKRuleCore_raw_sound (S C tag φ ψ θ k Γ Δ : ℕ)
    (hin : arithmeticLKInputs S C φ ψ θ Γ Δ)
    (hcore : arithmeticLKRuleCore S C tag φ ψ θ k Γ Δ)
    (hp : ∀ xs ∈ Nat.natToList S, Nonempty (Derivation (rawSequent xs))) :
    Nonempty (Derivation (rawSequent C)) := by
  unfold arithmeticLKInputs at hin
  simp only [arithmeticPair_nat, evalArithmetic_nat] at hin
  obtain ⟨_, _, hφ, hψ, hθ, hΓ, _⟩ := hin
  have hmem {xs : ℕ} (hm : listMember.eval (Nat.pair xs S) = 1) : Nonempty (Derivation (rawSequent xs)) :=
    hp xs ((listMember_natToList xs S).mp hm)
  have hz (s c : ℕ) : proofRewriteCode.eval (Nat.pair s (Nat.pair 0 c)) =
      proofRewriteAtZero.eval (Nat.pair s c) := by
    simpa only [arithmeticPair_nat, evalArithmetic_nat] using (evalArithmetic_proofRewriteAtZero (s : ℕ) c).symm
  unfold arithmeticLKRuleCore at hcore
  simp only [arithmeticPair_nat, evalArithmetic_nat,
    OfNat.ofNat, Zero.zero, One.one, Arithmetic.natCast_nat, Nat.add_assoc, Nat.reduceAdd, hz] at hcore
  split_ifs at hcore with h0 h1 h2 h3 h4 h5 h6 h7
  · rw [hcore, rawSequent_cons, rawSequent_cons, rawSequent_zero, rawFormula_negate hφ]
    exact ⟨Derivation.eta (rawFormula 0 φ)⟩
  · obtain ⟨ha, hb, hC⟩ := hcore
    rw [hC]
    have hpos := hmem ha
    have hneg := hmem hb
    rw [rawSequent_cons] at hpos
    rw [rawSequent_cons, rawFormula_negate hφ] at hneg
    obtain ⟨dp⟩ := hpos
    obtain ⟨dn⟩ := hneg
    rw [rawSequent_append]
    exact ⟨dp.cut dn⟩
  · obtain ⟨hd, hsub⟩ := hcore
    obtain ⟨d⟩ := hmem hd
    exact ⟨d.contraction (rawSequent_subset hsub)⟩
  · rw [hcore, rawSequent_cons, rawSequent_zero,
      (RawFormulaCode.verum (ξ := ℕ) (n := 0) 0).decode_raw]
    exact ⟨Derivation.verum⟩
  · obtain ⟨ha, hC⟩ := hcore
    rw [hC]
    have hpos := hmem ha
    rw [rawSequent_cons, rawSequent_cons] at hpos
    obtain ⟨d⟩ := hpos
    rw [rawSequent_cons, rawFormula_or hφ hψ]
    exact ⟨d.or⟩
  · obtain ⟨ha, hb, hC⟩ := hcore
    rw [hC]
    have hpos := hmem ha
    have hneg := hmem hb
    rw [rawSequent_cons] at hpos hneg
    obtain ⟨dp⟩ := hpos
    obtain ⟨dq⟩ := hneg
    rw [rawSequent_cons, rawFormula_and hφ hψ]
    exact ⟨dp.and dq⟩
  · obtain ⟨ha, hC⟩ := hcore
    rw [hC]
    have hpos := hmem ha
    rw [rawSequent_cons, rawFormula_free hθ, rawSequent_shift hΓ] at hpos
    obtain ⟨d⟩ := hpos
    rw [rawSequent_cons, rawFormula_all hθ]
    exact ⟨d.all⟩
  · obtain ⟨ha, hC⟩ := hcore
    rw [hC]
    have hpos := hmem ha
    rw [rawSequent_cons, rawFormula_subst k hθ] at hpos
    obtain ⟨d⟩ := hpos
    rw [rawSequent_cons, rawFormula_exs hθ]
    exact ⟨d.exs⟩

theorem lkRuleCheck_raw_sound (S C w : ℕ)
    (hcheck : lkRuleCheck.eval (Nat.pair S (Nat.pair C w)) = 1)
    (hp : ∀ xs ∈ Nat.natToList S, Nonempty (Derivation (rawSequent xs))) :
    Nonempty (Derivation (rawSequent C)) := by
  obtain ⟨tag, w1, rfl⟩ := rawPair_cases w
  obtain ⟨φ, w2, rfl⟩ := rawPair_cases w1
  obtain ⟨ψ, w3, rfl⟩ := rawPair_cases w2
  obtain ⟨θ, w4, rfl⟩ := rawPair_cases w3
  obtain ⟨k, w5, rfl⟩ := rawPair_cases w4
  obtain ⟨Γ, Δ, rfl⟩ := rawPair_cases w5
  have he := evalArithmetic_lkRuleCheck_eq_one (S : ℕ) C tag φ ψ θ k Γ Δ
  simp only [arithmeticPair_nat, evalArithmetic_nat] at he
  obtain ⟨hin, hcore⟩ := he.mp hcheck
  exact arithmeticLKRuleCore_raw_sound S C tag φ ψ θ k Γ Δ hin hcore hp

end ZFVP
