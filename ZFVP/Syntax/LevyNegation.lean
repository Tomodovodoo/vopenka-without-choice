import ZFVP.Syntax.LevyCodes
import ZFVP.Syntax.BoundedNegation

/-! Negation duality for the internal Levy code families. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsLevyFormulaCode.neg {p k} {n φ : V} (hφ : IsLevyFormulaCode p k n φ) :
    IsLevyFormulaCode p.dual k n (negateFormula membershipLanguageCode ∅ n φ) := by
  induction k generalizing p n φ with
  | zero => exact IsBoundedFormulaCode.neg hφ
  | succ k ih =>
    refine levyFormulaCode_successor_induction k p
      (fun n φ ↦ IsLevyFormulaCode p.dual (k + 1) n (negateFormula membershipLanguageCode ∅ n φ))
      (by definability) ?_ ?_ ?_ ?_ n φ hφ
    · intro q n φ hφ
      exact (ih hφ).raise
    · intro n hn φ ψ hφ hψ ihφ ihψ
      rw [negateFormula_and membershipLanguageCode_valid hn hφ.valid hψ.valid,
        negateFormula_or membershipLanguageCode_valid hn hφ.valid hψ.valid]
      exact ⟨ihφ.or ihψ, ihφ.and ihψ⟩
    · intro n hn i hi φ hφ ihφ
      rw [negateFormula_boundedAll hn hi hφ.valid, negateFormula_boundedExists hn hi hφ.valid]
      exact ⟨IsLevyFormulaCode.boundedExists hn hi ihφ, IsLevyFormulaCode.boundedAll hn hi ihφ⟩
    · intro n hn φ hφ ihφ
      cases p
      · change IsLevyFormulaCode .pi (k + 1) n (negateFormula membershipLanguageCode ∅ n (existsCode φ))
        rw [negateFormula_exists membershipLanguageCode_valid hn hφ.valid]
        exact IsLevyFormulaCode.quantifier hn ihφ
      · change IsLevyFormulaCode .sigma (k + 1) n (negateFormula membershipLanguageCode ∅ n (allCode φ))
        rw [negateFormula_all membershipLanguageCode_valid hn hφ.valid]
        exact IsLevyFormulaCode.quantifier hn ihφ

theorem isLevyFormulaCode_neg_iff {p k} {n φ : V} (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    IsLevyFormulaCode p.dual k n (negateFormula membershipLanguageCode ∅ n φ) ↔ IsLevyFormulaCode p k n φ := by
  constructor
  · intro h
    simpa only [LevyPolarity.dual_dual, negateFormula_involutive membershipLanguageCode_valid hφ] using h.neg
  · exact IsLevyFormulaCode.neg

end ZFVP
