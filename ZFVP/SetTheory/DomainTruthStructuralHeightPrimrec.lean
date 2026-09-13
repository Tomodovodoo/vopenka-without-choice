import ZFVP.SetTheory.FormulaStructuralHeight
import ZFVP.Syntax.PartialTruthDomains
import Mathlib.Computability.Primrec.Basic

/-! A primitive recursive height bound for the uniform partial-truth formulas. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

private theorem structuralHeight_ballMem {n : ℕ}
    (t : SetTheorySemiterm Empty n) (φ : SetTheorySemisentence (n + 1)) :
    formulaStructuralHeight (Semiformula.ballMem t φ) = formulaStructuralHeight φ + 2 := by
  change max 0 (formulaStructuralHeight φ) + 1 + 1 = _
  rw [Nat.zero_max]

/-- The fixed syntax occurring in the correctness recursion. -/
def domainTruthStructuralHeightBase : ℕ :=
  max (formulaStructuralHeight sequenceSupportFormula)
    (max (formulaStructuralHeight sigmaOneBoundedFamilyFormula)
      (max (formulaStructuralHeight boundedUnionFormula)
        (max (formulaStructuralHeight (sigmaOneLevyExtensionFormula .sigma))
          (max (formulaStructuralHeight (sigmaOneLevyExtensionFormula .pi))
            (max (formulaStructuralHeight boundedPairMemberFormula)
              (max (formulaStructuralHeight boundedFunctionFormula)
                (max (formulaStructuralHeight (sigmaOneMembershipModelTruthFormula true))
                  (formulaStructuralHeight piOneMembershipTruthFormula))))))))

private theorem le_max_nine (a b c d e f g h i : ℕ) :
    let K := max a (max b (max c (max d (max e (max f (max g (max h i)))))))
    a ≤ K ∧ b ≤ K ∧ c ≤ K ∧ d ≤ K ∧ e ≤ K ∧ f ≤ K ∧ g ≤ K ∧ h ≤ K ∧ i ≤ K := by
  dsimp only
  omega

private theorem height_base_bounds :
    formulaStructuralHeight sequenceSupportFormula ≤ domainTruthStructuralHeightBase ∧
    formulaStructuralHeight sigmaOneBoundedFamilyFormula ≤ domainTruthStructuralHeightBase ∧
    formulaStructuralHeight boundedUnionFormula ≤ domainTruthStructuralHeightBase ∧
    formulaStructuralHeight (sigmaOneLevyExtensionFormula .sigma) ≤ domainTruthStructuralHeightBase ∧
    formulaStructuralHeight (sigmaOneLevyExtensionFormula .pi) ≤ domainTruthStructuralHeightBase ∧
    formulaStructuralHeight boundedPairMemberFormula ≤ domainTruthStructuralHeightBase ∧
    formulaStructuralHeight boundedFunctionFormula ≤ domainTruthStructuralHeightBase ∧
    formulaStructuralHeight (sigmaOneMembershipModelTruthFormula true) ≤ domainTruthStructuralHeightBase ∧
    formulaStructuralHeight piOneMembershipTruthFormula ≤ domainTruthStructuralHeightBase :=
  le_max_nine _ _ _ _ _ _ _ _ _

private theorem familyHeightStep_le (K k a b u e : ℕ)
    (ha : a ≤ K + 6 * k) (hb : b ≤ K + 6 * k) (hu : u ≤ K) (he : e ≤ K) :
    max a (max b (max u e + 1 + 1) + 1 + 1) + 1 + 1 ≤ K + 6 * (k + 1) := by
  simp only [← Nat.add_max_add_right, Nat.max_le]
  omega

private theorem levyFamily_structuralHeight_le (k : ℕ) (p : LevyPolarity) :
    formulaStructuralHeight (sigmaOneLevyFamilyFormula k p) ≤
      domainTruthStructuralHeightBase + 6 * k := by
  induction k generalizing p with
  | zero =>
    simpa only [sigmaOneLevyFamilyFormula, Nat.mul_zero, Nat.add_zero] using height_base_bounds.2.1
  | succ k ih =>
    have hE : formulaStructuralHeight (sigmaOneLevyExtensionFormula p) ≤
        domainTruthStructuralHeightBase := by
      cases p
      · exact height_base_bounds.2.2.2.1
      · exact height_base_bounds.2.2.2.2.1
    simpa only [sigmaOneLevyFamilyFormula, formulaStructuralHeight, formulaStructuralHeight_rew] using
      familyHeightStep_le _ _ _ _ _ _ (ih .sigma) (ih .pi) height_base_bounds.2.2.1 hE

private theorem levyCode_structuralHeight_le (k : ℕ) :
    formulaStructuralHeight (sigmaOneLevyCodeFormula .sigma k) ≤
      domainTruthStructuralHeightBase + 6 * k + 2 := by
  have hb := height_base_bounds.2.2.2.2.2.1
  have hk : domainTruthStructuralHeightBase ≤ domainTruthStructuralHeightBase + 6 * k :=
    Nat.le_add_right _ _
  have hh := Nat.max_le.mpr ⟨levyFamily_structuralHeight_le k .sigma, hb.trans hk⟩
  simpa only [sigmaOneLevyCodeFormula, formulaStructuralHeight, formulaStructuralHeight_rew,
    Nat.add_assoc] using Nat.add_le_add_right (Nat.add_le_add_right hh 1) 1

private theorem correctHeightStep_le (K k d c f s p : ℕ)
    (hd : d ≤ K + 20 * k) (hc : c ≤ K + 6 * (k + 1) + 2)
    (hf : f ≤ K) (hs : s ≤ K) (hp : p ≤ K) :
    max d (max c (max f (max (max d (max f s + 1) + 1 + 1) p + 1) + 1) + 1 + 2 + 2 + 2) + 1 ≤
      K + 20 * (k + 1) := by
  simp only [← Nat.add_max_add_right, Nat.max_le]
  omega

theorem correctDomainFormula_structuralHeight_le (k : ℕ) :
    formulaStructuralHeight (correctDomainFormula k) ≤ domainTruthStructuralHeightBase + 20 * k := by
  induction k with
  | zero =>
    simpa only [correctDomainFormula, Nat.mul_zero, Nat.add_zero] using height_base_bounds.1
  | succ k ih =>
    simpa only [correctDomainFormula, domainSigmaTruthFormula, structuralHeight_ballMem,
      formulaStructuralHeight, Semiformula.imp_eq, formulaStructuralHeight_neg,
      formulaStructuralHeight_rew] using
      correctHeightStep_le _ _ _ _ _ _ _ ih (levyCode_structuralHeight_le (k + 1))
        height_base_bounds.2.2.2.2.2.2.1 height_base_bounds.2.2.2.2.2.2.2.1
        height_base_bounds.2.2.2.2.2.2.2.2

/-- A linear bound whose coefficient covers the quantifiers and Boolean nodes
introduced by one correctness step. -/
def domainTruthStructuralHeightBound (k : ℕ) : ℕ :=
  domainTruthStructuralHeightBase + 20 * (k + 1)

theorem domainTruthStructuralHeightBound_primrec : Primrec domainTruthStructuralHeightBound :=
  Primrec.nat_add.comp (Primrec.const _)
    (Primrec.nat_mul.comp (Primrec.const 20) Primrec.succ)

private theorem truthHeightStep_le (K k d f s : ℕ)
    (hd : d ≤ K + 20 * k) (hf : f ≤ K) (hs : s ≤ K) :
    max d (max f s + 1) + 1 + 1 ≤ K + 20 * (k + 1) := by
  simp only [← Nat.add_max_add_right, Nat.max_le]
  omega

theorem domainTruthFormula_structuralHeight_le (k : ℕ) :
    formulaStructuralHeight (domainTruthFormula .sigma k) ≤ domainTruthStructuralHeightBound k := by
  simpa only [domainTruthFormula, domainSigmaTruthFormula, formulaStructuralHeight,
    formulaStructuralHeight_rew, domainTruthStructuralHeightBound] using
    truthHeightStep_le _ _ _ _ _ (correctDomainFormula_structuralHeight_le k)
      height_base_bounds.2.2.2.2.2.2.1 height_base_bounds.2.2.2.2.2.2.2.1

end ZFVP
