import ZFVP.Syntax.PartialTruthDomains

/-! Internal Boolean, negation and bounded-quantifier equations for every positive partial-truth level. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem domainTruth_and {p : LevyPolarity} {k : ℕ} {n φ ψ b : V}
    (hφ : IsLevyFormulaCode p (k + 1) n φ) (hψ : IsLevyFormulaCode p (k + 1) n ψ)
    (hb : IsFunction b ∧ domain b = n) :
    DomainTruth p k n (andCode φ ψ) b ↔ DomainTruth p k n φ b ∧ DomainTruth p k n ψ b := by
  obtain ⟨A, hA, hbA⟩ := correctDomain_assignment (k + 1) hb
  rw [hA.truth_iff (hφ.and hψ) hbA, hA.truth_iff hφ hbA, hA.truth_iff hψ hbA]
  exact satisfies_and membershipLanguageCode_valid hφ.context hφ.valid hψ.valid (by simpa using hbA)

theorem domainTruth_or {p : LevyPolarity} {k : ℕ} {n φ ψ b : V}
    (hφ : IsLevyFormulaCode p (k + 1) n φ) (hψ : IsLevyFormulaCode p (k + 1) n ψ)
    (hb : IsFunction b ∧ domain b = n) :
    DomainTruth p k n (orCode φ ψ) b ↔ DomainTruth p k n φ b ∨ DomainTruth p k n ψ b := by
  obtain ⟨A, hA, hbA⟩ := correctDomain_assignment (k + 1) hb
  rw [hA.truth_iff (hφ.or hψ) hbA, hA.truth_iff hφ hbA, hA.truth_iff hψ hbA]
  exact satisfies_or membershipLanguageCode_valid hφ.context hφ.valid hψ.valid (by simpa using hbA)

theorem domainTruth_negate {p : LevyPolarity} {k : ℕ} {n φ b : V}
    (hφ : IsLevyFormulaCode p (k + 1) n φ) (hb : IsFunction b ∧ domain b = n) :
    DomainTruth p.dual k n (negateFormula membershipLanguageCode ∅ n φ) b ↔ ¬DomainTruth p k n φ b := by
  obtain ⟨A, hA, hbA⟩ := correctDomain_assignment (k + 1) hb
  rw [hA.truth_iff hφ.neg hbA, hA.truth_iff hφ hbA]
  exact satisfies_negateFormula membershipLanguageCode_valid hφ.valid (by simpa using hbA)

theorem domainTruth_boundedAll {p : LevyPolarity} {k : ℕ} {n i φ b : V}
    (hn : n ∈ (ω : V)) (hi : i ∈ n) (hφ : IsLevyFormulaCode p (k + 1) (succ n) φ)
    (hb : IsFunction b ∧ domain b = n) :
    DomainTruth p k n (boundedAllCode i φ) b ↔
      ∀ x ∈ b ‘ i, DomainTruth p k (succ n) φ (assignmentPrepend n b x) := by
  obtain ⟨A, hA, hbA⟩ := correctDomain_assignment (k + 1) hb
  let := hA.support
  rw [hA.truth_iff (IsLevyFormulaCode.boundedAll hn hi hφ) hbA,
    membershipSatisfies_boundedAll hn hi hφ.valid hbA]
  exact forall_congr' fun x ↦ imp_congr_right fun hx ↦
    (hA.truth_iff hφ (assignmentPrepend_mem_function hn hbA
      (hA.support.mem_trans hx (function_value_mem hbA hi)))).symm

theorem domainTruth_boundedExists {p : LevyPolarity} {k : ℕ} {n i φ b : V}
    (hn : n ∈ (ω : V)) (hi : i ∈ n) (hφ : IsLevyFormulaCode p (k + 1) (succ n) φ)
    (hb : IsFunction b ∧ domain b = n) :
    DomainTruth p k n (boundedExistsCode i φ) b ↔
      ∃ x ∈ b ‘ i, DomainTruth p k (succ n) φ (assignmentPrepend n b x) := by
  obtain ⟨A, hA, hbA⟩ := correctDomain_assignment (k + 1) hb
  let := hA.support
  rw [hA.truth_iff (IsLevyFormulaCode.boundedExists hn hi hφ) hbA,
    membershipSatisfies_boundedExists hn hi hφ.valid hbA]
  exact exists_congr fun x ↦ and_congr_right fun hx ↦
    (hA.truth_iff hφ (assignmentPrepend_mem_function hn hbA
      (hA.support.mem_trans hx (function_value_mem hbA hi)))).symm

theorem domainSigmaTruth_exists {k : ℕ} {n φ b : V} (hn : n ∈ (ω : V))
    (hφ : IsLevyFormulaCode .sigma (k + 1) (succ n) φ) (hb : IsFunction b ∧ domain b = n) :
    DomainSigmaTruth k n (existsCode φ) b ↔
      ∃ x : V, DomainSigmaTruth k (succ n) φ (assignmentPrepend n b x) := by
  have hparent : IsLevyFormulaCode .sigma (k + 1) n (existsCode φ) := IsLevyFormulaCode.quantifier hn hφ
  constructor
  · intro ht
    obtain ⟨A, hA, hbA⟩ := correctDomain_assignment (k + 1) hb
    have hs := (hA.sigmaTruth_iff hparent hbA).mp ht
    have he := (satisfies_exists membershipLanguageCode_valid hn hφ.valid (by simpa using hbA)).mp hs
    obtain ⟨x, hx, hsx⟩ := he
    have hxA : x ∈ A := by simpa using hx
    exact ⟨x, (hA.sigmaTruth_iff hφ (assignmentPrepend_mem_function hn hbA hxA)).mpr hsx⟩
  · rintro ⟨x, ht⟩
    obtain ⟨A, hA, hbA, hxA⟩ := correctDomain_assignment_with (k + 1) hb x
    apply (hA.sigmaTruth_iff hparent hbA).mpr
    apply (satisfies_exists membershipLanguageCode_valid hn hφ.valid (by simpa using hbA)).mpr
    exact ⟨x, by simpa using hxA,
      (hA.sigmaTruth_iff hφ (assignmentPrepend_mem_function hn hbA hxA)).mp ht⟩

theorem domainPiTruth_all {k : ℕ} {n φ b : V} (hn : n ∈ (ω : V))
    (hφ : IsLevyFormulaCode .pi (k + 1) (succ n) φ) (hb : IsFunction b ∧ domain b = n) :
    DomainPiTruth k n (allCode φ) b ↔
      ∀ x : V, DomainPiTruth k (succ n) φ (assignmentPrepend n b x) := by
  have hparent : IsLevyFormulaCode .pi (k + 1) n (allCode φ) := IsLevyFormulaCode.quantifier hn hφ
  constructor
  · intro ht x
    obtain ⟨A, hA, hbA, hxA⟩ := correctDomain_assignment_with (k + 1) hb x
    apply (hA.piTruth_iff hφ (assignmentPrepend_mem_function hn hbA hxA)).mpr
    have hs := (hA.piTruth_iff hparent hbA).mp ht
    exact (satisfies_all membershipLanguageCode_valid hn hφ.valid (by simpa using hbA)).mp hs x (by simpa using hxA)
  · intro ht
    obtain ⟨A, hA, hbA⟩ := correctDomain_assignment (k + 1) hb
    apply (hA.piTruth_iff hparent hbA).mpr
    apply (satisfies_all membershipLanguageCode_valid hn hφ.valid (by simpa using hbA)).mpr
    intro x hx
    have hxA : x ∈ A := by simpa using hx
    exact (hA.piTruth_iff hφ (assignmentPrepend_mem_function hn hbA hxA)).mp (ht x)

end ZFVP
