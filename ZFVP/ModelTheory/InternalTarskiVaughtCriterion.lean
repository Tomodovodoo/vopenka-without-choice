import ZFVP.ModelTheory.DirectedElementaryUnion

/-! An internal Tarski--Vaught criterion, including nonstandard formula codes. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem elementaryInclusion_of_witness_closure {X B : V}
    (hX : IsNonempty X) (hB : IsNonempty B) (hsub : X ⊆ B)
    (hpos : ∀ n ∈ (ω : V), ∀ φ ∈ formulaSet membershipLanguageCode ∅ (succ n),
      ∀ b ∈ X ^ n,
      (∃ x ∈ B, MembershipSatisfies B (succ n) φ (assignmentPrepend n b x)) →
      ∃ x ∈ X, MembershipSatisfies B (succ n) φ (assignmentPrepend n b x))
    (hneg : ∀ n ∈ (ω : V), ∀ φ ∈ formulaSet membershipLanguageCode ∅ (succ n),
      ∀ b ∈ X ^ n,
      (∃ x ∈ B, ¬MembershipSatisfies B (succ n) φ (assignmentPrepend n b x)) →
      ∃ x ∈ X, ¬MembershipSatisfies B (succ n) φ (assignmentPrepend n b x)) :
    IsElementaryInclusion X B := by
  classical
  have hmain : ∀ n φ, φ ∈ formulaSet membershipLanguageCode ∅ n → ∀ b ∈ X ^ n,
      MembershipSatisfies X n φ b ↔ MembershipSatisfies B n φ b := by
    apply formulaSet_induction membershipLanguageCode_valid ∅
      (fun n φ ↦ ∀ b ∈ X ^ n, MembershipSatisfies X n φ b ↔ MembershipSatisfies B n φ b)
      (by definability)
    · intro n hn
      constructor
      · intro b hb
        have hbB := mem_function_of_mem_function_of_subset hb hsub
        change Satisfies _ _ _ _ _ _ _ ↔ Satisfies _ _ _ _ _ _ _
        rw [satisfies_truth membershipLanguageCode_valid hn, satisfies_truth membershipLanguageCode_valid hn]
        exact iff_of_true (by simpa using hb) (by simpa using hbB)
      · intro b hb
        exact iff_of_false (not_satisfies_falsity membershipLanguageCode_valid hn)
          (not_satisfies_falsity membershipLanguageCode_valid hn)
    · intro n hn r args ha
      constructor
      · intro b hb
        have hbB := mem_function_of_mem_function_of_subset hb hsub
        change Satisfies _ _ _ _ _ _ _ ↔ Satisfies _ _ _ _ _ _ _
        rw [satisfies_atom membershipLanguageCode_valid hn ha (by simpa using hb),
          satisfies_atom membershipLanguageCode_valid hn ha (by simpa using hbB)]
        exact membershipAtomicHolds_iff hn hX hB hb hbB ha
      · intro b hb
        have hbB := mem_function_of_mem_function_of_subset hb hsub
        change Satisfies _ _ _ _ _ _ _ ↔ Satisfies _ _ _ _ _ _ _
        rw [satisfies_negAtom membershipLanguageCode_valid hn ha (by simpa using hb),
          satisfies_negAtom membershipLanguageCode_valid hn ha (by simpa using hbB)]
        exact not_congr (membershipAtomicHolds_iff hn hX hB hb hbB ha)
    · intro n hn φ ψ hφ hψ ihφ ihψ
      constructor
      · intro b hb
        have hbB := mem_function_of_mem_function_of_subset hb hsub
        change Satisfies _ _ _ _ _ _ _ ↔ Satisfies _ _ _ _ _ _ _
        rw [satisfies_and membershipLanguageCode_valid hn hφ hψ (by simpa using hb),
          satisfies_and membershipLanguageCode_valid hn hφ hψ (by simpa using hbB)]
        exact and_congr (ihφ b hb) (ihψ b hb)
      · intro b hb
        have hbB := mem_function_of_mem_function_of_subset hb hsub
        change Satisfies _ _ _ _ _ _ _ ↔ Satisfies _ _ _ _ _ _ _
        rw [satisfies_or membershipLanguageCode_valid hn hφ hψ (by simpa using hb),
          satisfies_or membershipLanguageCode_valid hn hφ hψ (by simpa using hbB)]
        exact or_congr (ihφ b hb) (ihψ b hb)
    · intro n hn φ hφ ih
      constructor
      · intro b hb
        have hbB := mem_function_of_mem_function_of_subset hb hsub
        rw [membershipSatisfies_all hn hφ hb, membershipSatisfies_all hn hφ hbB]
        constructor
        · intro hall x hx
          by_contra hnot
          obtain ⟨y, hy, hny⟩ := hneg n hn φ hφ b hb ⟨x, hx, hnot⟩
          exact hny ((ih _ (assignmentPrepend_mem_function hn hb hy)).mp (hall y hy))
        · intro hall x hx
          exact (ih _ (assignmentPrepend_mem_function hn hb hx)).mpr (hall x (hsub x hx))
      · intro b hb
        have hbB := mem_function_of_mem_function_of_subset hb hsub
        rw [membershipSatisfies_exists hn hφ hb, membershipSatisfies_exists hn hφ hbB]
        constructor
        · rintro ⟨x, hx, hh⟩
          exact ⟨x, hsub x hx, (ih _ (assignmentPrepend_mem_function hn hb hx)).mp hh⟩
        · intro hex
          obtain ⟨x, hx, hh⟩ := hpos n hn φ hφ b hb hex
          exact ⟨x, hx, (ih _ (assignmentPrepend_mem_function hn hb hx)).mpr hh⟩
  apply IsElementaryInclusion.of_satisfaction hX hB hsub
  intro n _ φ hφ b hb
  exact hmain n φ ((mem_formulaSet_iff _ _ _ _).mpr hφ) b hb

theorem elementaryInclusion_of_boolean_witness_closure {X B : V}
    (hX : IsNonempty X) (hB : IsNonempty B) (hsub : X ⊆ B)
    (hclose : ∀ n ∈ (ω : V), ∀ φ ∈ formulaSet membershipLanguageCode ∅ (succ n),
      ∀ b ∈ X ^ n, ∀ t : Bool,
      (∃ x ∈ B, (MembershipSatisfies B (succ n) φ (assignmentPrepend n b x) ↔ t = true)) →
      ∃ x ∈ X, (MembershipSatisfies B (succ n) φ (assignmentPrepend n b x) ↔ t = true)) :
    IsElementaryInclusion X B := by
  apply elementaryInclusion_of_witness_closure hX hB hsub
  · intro n hn φ hφ b hb hex
    simpa using hclose n hn φ hφ b hb true (by simpa using hex)
  · intro n hn φ hφ b hb hex
    simpa using hclose n hn φ hφ b hb false (by simpa using hex)

end ZFVP
