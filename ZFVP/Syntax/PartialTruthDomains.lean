import ZFVP.SetTheory.CorrectDomainClosure

/-! The two partial-truth polarities evaluated in sufficiently correct set domains. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def domainTruthFormula (p : LevyPolarity) (k : ℕ) : SetTheorySemisentence 3 :=
  match p with
  | .sigma => domainSigmaTruthFormula (correctDomainFormula k)
  | .pi => domainPiTruthFormula (correctDomainFormula k)

theorem domainTruthFormula_levy (p : LevyPolarity) (k : ℕ) :
    IsLevyFormula p (k + 1) (domainTruthFormula p k) := by
  cases p
  · exact domainSigmaTruthFormula_exact_complexity k
  · exact domainPiTruthFormula_exact_complexity k

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def DomainTruth (p : LevyPolarity) (k : ℕ) (n φ b : V) : Prop :=
  match p with
  | .sigma => DomainSigmaTruth k n φ b
  | .pi => DomainPiTruth k n φ b

theorem eval_domainTruthFormula (p : LevyPolarity) (k : ℕ) (n φ b : V) :
    (domainTruthFormula p k).Evalb ![n, φ, b] ↔ DomainTruth p k n φ b := by
  cases p
  · exact eval_domainSigmaTruthFormula k n φ b
  · exact eval_domainPiTruthFormula k n φ b

theorem CorrectDomain.piTruth_iff {k : ℕ} {A n φ b : V} (hA : CorrectDomain (k + 1) A)
    (hφ : IsLevyFormulaCode .pi (k + 1) n φ) (hb : b ∈ A ^ n) :
    DomainPiTruth k n φ b ↔ MembershipSatisfies A n φ b := by
  have hvalid : IsMembershipFormulaCode n φ := (mem_formulaSet_iff _ _ _ _).mp hφ.valid
  rw [domainPiTruth_iff_not_sigma_negate k hvalid, hA.sigmaTruth_iff hφ.neg hb]
  have hb' : b ∈ structureDomain (membershipStructureCode A) ^ n := by simpa using hb
  change (¬Satisfies membershipLanguageCode ∅ (membershipStructureCode A) ∅ n
    (negateFormula membershipLanguageCode ∅ n φ) b) ↔ _
  rw [satisfies_negateFormula membershipLanguageCode_valid hφ.valid hb', not_not]
  rfl

theorem CorrectDomain.truth_iff {p : LevyPolarity} {k : ℕ} {A n φ b : V}
    (hA : CorrectDomain (k + 1) A) (hφ : IsLevyFormulaCode p (k + 1) n φ) (hb : b ∈ A ^ n) :
    DomainTruth p k n φ b ↔ MembershipSatisfies A n φ b := by
  cases p
  · exact hA.sigmaTruth_iff hφ hb
  · exact hA.piTruth_iff hφ hb

theorem correctDomain_assignment (k : ℕ) {n b : V} (hb : IsFunction b ∧ domain b = n) :
    ∃ A : V, CorrectDomain k A ∧ b ∈ A ^ n := by
  obtain ⟨A, hA, hbA⟩ := correctDomain_containing k b
  let := hA.support
  exact ⟨A, hA, (function_on_support_iff hbA n).mpr hb⟩

theorem correctDomain_assignment_with (k : ℕ) {n b : V}
    (hb : IsFunction b ∧ domain b = n) (x : V) :
    ∃ A : V, CorrectDomain k A ∧ b ∈ A ^ n ∧ x ∈ A := by
  obtain ⟨A, hA, hp⟩ := correctDomain_containing k ⟨b, x⟩ₖ
  let := hA.support
  obtain ⟨hbA, hxA⟩ := kpair_components_mem_transitive hp
  exact ⟨A, hA, (function_on_support_iff hbA n).mpr hb, hxA⟩

theorem domainTruth_stable {p : LevyPolarity} {k l : ℕ} (hkl : k ≤ l) {n φ b : V}
    (hφ : IsLevyFormulaCode p (k + 1) n φ) :
    DomainTruth p k n φ b ↔ DomainTruth p l n φ b := by
  cases p
  · exact domainSigmaTruth_stable hkl hφ
  · exact domainPiTruth_stable hkl hφ

theorem domainTruth_standard_correct {p : LevyPolarity} {k n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsLevyFormula p (k + 1) φ) (v : Fin n → V) :
    DomainTruth p k (n : V) (encodeMembershipFormula φ) (standardTuple v) ↔ φ.Evalb v := by
  cases p
  · exact domainSigmaTruth_correct k hφ v
  · exact domainPiTruth_correct k hφ v

end ZFVP
