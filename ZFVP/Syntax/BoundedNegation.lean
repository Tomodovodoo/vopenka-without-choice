import ZFVP.Syntax.NegationSemantics
import ZFVP.Syntax.BoundedSatisfaction

/-! Internal bounded codes are closed under negation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem negateFormula_boundedAll {n i φ : V} (hn : n ∈ (ω : V)) (hi : i ∈ n)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) :
    negateFormula membershipLanguageCode ∅ n (boundedAllCode i φ) =
      boundedExistsCode i (negateFormula membershipLanguageCode ∅ (succ n) φ) := by
  have hg := boundedGuardArguments_valid hn hi
  have hgφ := (formulaSet_atoms membershipLanguageCode_valid (ω_succ_closed hn) hg).2
  rw [boundedAllCode, boundedExistsCode,
    negateFormula_all membershipLanguageCode_valid hn
      (formulaSet_binary membershipLanguageCode_valid (ω_succ_closed hn) hgφ hφ).2,
    negateFormula_or membershipLanguageCode_valid (ω_succ_closed hn) hgφ hφ,
    negateFormula_negAtom membershipLanguageCode_valid (ω_succ_closed hn) hg]

theorem negateFormula_boundedExists {n i φ : V} (hn : n ∈ (ω : V)) (hi : i ∈ n)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) :
    negateFormula membershipLanguageCode ∅ n (boundedExistsCode i φ) =
      boundedAllCode i (negateFormula membershipLanguageCode ∅ (succ n) φ) := by
  have hg := boundedGuardArguments_valid hn hi
  have hgφ := (formulaSet_atoms membershipLanguageCode_valid (ω_succ_closed hn) hg).1
  rw [boundedAllCode, boundedExistsCode,
    negateFormula_exists membershipLanguageCode_valid hn
      (formulaSet_binary membershipLanguageCode_valid (ω_succ_closed hn) hgφ hφ).1,
    negateFormula_and membershipLanguageCode_valid (ω_succ_closed hn) hgφ hφ,
    negateFormula_atom membershipLanguageCode_valid (ω_succ_closed hn) hg]

theorem IsBoundedFormulaCode.neg {n φ : V} (hφ : IsBoundedFormulaCode n φ) :
    IsBoundedFormulaCode n (negateFormula membershipLanguageCode ∅ n φ) := by
  suffices h : ∀ p ∈ (boundedFormulaFamily : V),
      IsBoundedFormulaCode (kpair.π₁ p) (negateFormula membershipLanguageCode ∅ (kpair.π₁ p) (kpair.π₂ p)) by
    simpa using h ⟨n, φ⟩ₖ hφ
  refine boundedFormulaFamily_induction
    (fun p : V ↦ IsBoundedFormulaCode (kpair.π₁ p)
      (negateFormula membershipLanguageCode ∅ (kpair.π₁ p) (kpair.π₂ p))) (by definability) ?_ ?_ ?_ ?_
  all_goals simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  · intro n hn
    rw [negateFormula_truth membershipLanguageCode_valid hn, negateFormula_falsity membershipLanguageCode_valid hn]
    exact (boundedFormulaFamily_closed n hn).1.symm
  · intro n hn r args ha
    rw [negateFormula_atom membershipLanguageCode_valid hn ha, negateFormula_negAtom membershipLanguageCode_valid hn ha]
    exact ((boundedFormulaFamily_closed n hn).2.1 r args ha).symm
  · intro n hn φ ψ hφ hψ ihφ ihψ
    rw [negateFormula_and membershipLanguageCode_valid hn (IsBoundedFormulaCode.valid hφ) (IsBoundedFormulaCode.valid hψ),
      negateFormula_or membershipLanguageCode_valid hn (IsBoundedFormulaCode.valid hφ) (IsBoundedFormulaCode.valid hψ)]
    exact ((boundedFormulaFamily_closed n hn).2.2.1 _ _ ihφ ihψ).symm
  · intro n hn i hi φ hφ ih
    rw [negateFormula_boundedAll hn hi (IsBoundedFormulaCode.valid hφ),
      negateFormula_boundedExists hn hi (IsBoundedFormulaCode.valid hφ)]
    exact ((boundedFormulaFamily_closed n hn).2.2.2 i hi _ ih).symm

theorem isBoundedFormulaCode_neg_iff {n φ : V} (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    IsBoundedFormulaCode n (negateFormula membershipLanguageCode ∅ n φ) ↔ IsBoundedFormulaCode n φ := by
  constructor
  · intro h
    simpa only [negateFormula_involutive membershipLanguageCode_valid hφ] using h.neg
  · exact IsBoundedFormulaCode.neg

theorem boundedTruth_negateFormula {n φ b : V} [IsFunction b] (hb : domain b = n)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    BoundedTruth n (negateFormula membershipLanguageCode ∅ n φ) b ↔ ¬BoundedTruth n φ b :=
  satisfies_negateFormula membershipLanguageCode_valid hφ (by simpa using assignment_mem_boundedTruthDomain hb)

theorem sigmaOneTruth_negateFormula {n φ b : V} (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    SigmaOneTruth n (negateFormula membershipLanguageCode ∅ n φ) b ↔ ¬PiOneTruth n φ b := by
  classical
  unfold SigmaOneTruth PiOneTruth
  simp only [not_forall, exists_prop]
  apply exists_congr
  intro A
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro hb
  exact satisfies_negateFormula membershipLanguageCode_valid hφ (by simpa using hb)

theorem piOneTruth_negateFormula {n φ b : V} (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    PiOneTruth n (negateFormula membershipLanguageCode ∅ n φ) b ↔ ¬SigmaOneTruth n φ b := by
  classical
  unfold SigmaOneTruth PiOneTruth
  simp only [not_exists, not_and]
  apply forall_congr'
  intro A
  apply forall_congr'
  intro _
  apply forall_congr'
  intro _
  apply forall_congr'
  intro hb
  exact satisfies_negateFormula membershipLanguageCode_valid hφ (by simpa using hb)

end ZFVP
