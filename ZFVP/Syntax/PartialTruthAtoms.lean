import ZFVP.Syntax.PartialTruthConnectives

/-! Constants, atomic formulas and level changes for internal partial truth. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem domainTruth_bounded {p : LevyPolarity} {k : ℕ} {n φ b : V}
    (hφ : IsBoundedFormulaCode n φ) (hb : IsFunction b ∧ domain b = n) :
    DomainTruth p k n φ b ↔ BoundedTruth n φ b := by
  obtain ⟨A, hA, hbA⟩ := correctDomain_assignment (k + 1) hb
  let := hA.support
  exact (hA.truth_iff (.bounded hφ) hbA).trans
    (boundedTruth_iff_membershipSatisfies hφ hA.nonempty hbA).symm

theorem domainTruth_truth (p : LevyPolarity) (k : ℕ) {n b : V}
    (hn : n ∈ (ω : V)) (hb : IsFunction b ∧ domain b = n) : DomainTruth p k n truthCode b := by
  obtain ⟨A, hA, hbA⟩ := correctDomain_assignment (k + 1) hb
  have hcode : IsLevyFormulaCode p (k + 1) n truthCode :=
    .bounded (boundedFormulaFamily_closed n hn).1.1
  apply (hA.truth_iff hcode hbA).mpr
  exact (satisfies_truth membershipLanguageCode_valid hn).mpr (by simpa using hbA)

theorem domainTruth_falsity (p : LevyPolarity) (k : ℕ) {n b : V}
    (hn : n ∈ (ω : V)) (hb : IsFunction b ∧ domain b = n) : ¬DomainTruth p k n falsityCode b := by
  obtain ⟨A, hA, hbA⟩ := correctDomain_assignment (k + 1) hb
  have hcode : IsLevyFormulaCode p (k + 1) n falsityCode :=
    .bounded (boundedFormulaFamily_closed n hn).1.2
  intro h
  exact not_satisfies_falsity membershipLanguageCode_valid hn ((hA.truth_iff hcode hbA).mp h)

theorem domainTruth_atoms (p : LevyPolarity) (k : ℕ) {n r args b : V}
    (hn : n ∈ (ω : V)) (ha : IsMembershipAtomicArguments n r args)
    (hb : IsFunction b ∧ domain b = n) :
    (DomainTruth p k n (atomCode r args) b ↔ DirectMembershipAtomicHolds n b r args) ∧
    (DomainTruth p k n (negAtomCode r args) b ↔ ¬DirectMembershipAtomicHolds n b r args) := by
  obtain ⟨A, hA, hbA⟩ := correctDomain_assignment (k + 1) hb
  have ha' := (membershipAtomicArguments_iff hn).mpr ha
  have hcodes := (boundedFormulaFamily_closed n hn).2.1 r args ha'
  have hpos : IsLevyFormulaCode p (k + 1) n (atomCode r args) := .bounded hcodes.1
  have hneg : IsLevyFormulaCode p (k + 1) n (negAtomCode r args) := .bounded hcodes.2
  rw [hA.truth_iff hpos hbA, hA.truth_iff hneg hbA, directMembershipAtomicHolds_iff hn hbA ha]
  exact ⟨satisfies_atom membershipLanguageCode_valid hn ha' (by simpa using hbA),
    satisfies_negAtom membershipLanguageCode_valid hn ha' (by simpa using hbA)⟩

theorem domainTruth_raise {p q : LevyPolarity} {k : ℕ} {n φ b : V}
    (hφ : IsLevyFormulaCode p (k + 1) n φ) (hb : IsFunction b ∧ domain b = n) :
    DomainTruth q (k + 1) n φ b ↔ DomainTruth p k n φ b := by
  obtain ⟨A, hA, hbA⟩ := correctDomain_assignment (k + 2) hb
  exact (hA.truth_iff hφ.raise hbA).trans (hA.lower.truth_iff hφ hbA).symm

end ZFVP
