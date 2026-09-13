import ZFVP.ModelTheory.LocalPartialTruthQuantifiers

/-! Partial truth in a transitive ZF model agrees with its full internal satisfaction relation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem localDomainTruth_correct_of_lower (U : V) [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (k : ℕ) (p : LevyPolarity)
    (hbase : ∀ q n φ, IsLevyFormulaCode q k n φ → ∀ b ∈ U ^ n,
      LocalDomainTruth U p k n φ b ↔ MembershipSatisfies U n φ b) :
    ∀ n φ, IsLevyFormulaCode p (k + 1) n φ → ∀ b ∈ U ^ n,
      LocalDomainTruth U p k n φ b ↔ MembershipSatisfies U n φ b := by
  apply levyFormulaCode_successor_induction k p
    (fun n φ ↦ ∀ b ∈ U ^ n, LocalDomainTruth U p k n φ b ↔ MembershipSatisfies U n φ b)
    (by definability) hbase
  · intro n hn φ ψ hφ hψ ihφ ihψ
    constructor
    · intro b hb
      rw [LocalDomainTruth.and_iff U hφ hψ hb, ihφ b hb, ihψ b hb]
      exact (satisfies_and (M := membershipStructureCode U) (e := ∅)
        membershipLanguageCode_valid hn hφ.valid hψ.valid (by simpa using hb)).symm
    · intro b hb
      rw [LocalDomainTruth.or_iff U hφ hψ hb, ihφ b hb, ihψ b hb]
      exact (satisfies_or (M := membershipStructureCode U) (e := ∅)
        membershipLanguageCode_valid hn hφ.valid hψ.valid (by simpa using hb)).symm
  · intro n hn i hi φ hφ ih
    constructor
    · intro b hb
      rw [LocalDomainTruth.boundedAll_iff U hn hi hφ hb, membershipSatisfies_boundedAll hn hi hφ.valid hb]
      exact forall_congr' fun x ↦ imp_congr_right fun hx ↦ ih _
        (assignmentPrepend_mem_function hn hb
          ((inferInstance : IsTransitive U).mem_trans hx (function_value_mem hb hi)))
    · intro b hb
      rw [LocalDomainTruth.boundedExists_iff U hn hi hφ hb, membershipSatisfies_boundedExists hn hi hφ.valid hb]
      exact exists_congr fun x ↦ and_congr_right fun hx ↦ ih _
        (assignmentPrepend_mem_function hn hb
          ((inferInstance : IsTransitive U).mem_trans hx (function_value_mem hb hi)))
  · intro n hn φ hφ ih b hb
    cases p with
    | sigma =>
      change LocalDomainTruth U .sigma k n (existsCode φ) b ↔ MembershipSatisfies U n (existsCode φ) b
      rw [LocalDomainTruth.exists_iff U hn hφ hb, membershipSatisfies_exists hn hφ.valid hb]
      exact exists_congr fun x ↦ and_congr_right fun hx ↦ ih _ (assignmentPrepend_mem_function hn hb hx)
    | pi =>
      change LocalDomainTruth U .pi k n (allCode φ) b ↔ MembershipSatisfies U n (allCode φ) b
      rw [LocalDomainTruth.all_iff U hn hφ hb, membershipSatisfies_all hn hφ.valid hb]
      exact forall_congr' fun x ↦ imp_congr_right fun hx ↦ ih _ (assignmentPrepend_mem_function hn hb hx)

theorem localDomainTruth_correct (U : V) [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (k : ℕ) :
    ∀ p n φ, IsLevyFormulaCode p (k + 1) n φ → ∀ b ∈ U ^ n,
      LocalDomainTruth U p k n φ b ↔ MembershipSatisfies U n φ b := by
  induction k with
  | zero =>
    intro p
    apply localDomainTruth_correct_of_lower U 0 p
    intro q n φ hφ b hb
    exact LocalDomainTruth.bounded U ((isLevyFormulaCode_zero_iff q n φ).mp hφ) hb
  | succ k ih =>
    intro p
    apply localDomainTruth_correct_of_lower U (k + 1) p
    intro q n φ hφ b hb
    exact (LocalDomainTruth.raise_iff U hφ hb).trans (ih q n φ hφ b hb)

theorem TransitiveZF.domainTruth_iff (U : V) [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    {p : LevyPolarity} {k : ℕ} (n φ b : SetDomain U)
    (hφ : IsLevyFormulaCode p (k + 1) n φ) (hb : IsFunction b ∧ domain b = n) :
    DomainTruth p k n φ b ↔ MembershipSatisfies U n.val φ.val b.val := by
  let := TransitiveZF.sequenceSupport U
  have hφV := (TransitiveZF.levyCode_iff U p (k + 1) n φ).mp hφ
  have hbV := (TransitiveZF.function_on_iff U b n).mp hb
  have hbU := (function_on_support_iff b.property n.val).mpr hbV
  exact (localDomainTruth_iff U p k n φ b).symm.trans (localDomainTruth_correct U k p _ _ hφV _ hbU)

end ZFVP
