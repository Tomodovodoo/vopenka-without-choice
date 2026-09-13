import ZFVP.ModelTheory.ElementaryInclusionLaws

/-! Directed unions of internal elementary membership inclusions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem membershipSatisfies_all {A n φ b : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) (hb : b ∈ A ^ n) :
    MembershipSatisfies A n (allCode φ) b ↔
      ∀ x ∈ A, MembershipSatisfies A (succ n) φ (assignmentPrepend n b x) := by
  simpa only [MembershipSatisfies, membershipSatisfactionGraph, Satisfies, membershipStructureCode_domain] using
    satisfies_all (M := membershipStructureCode A) (e := ∅) membershipLanguageCode_valid hn hφ (by simpa using hb)

theorem membershipSatisfies_exists {A n φ b : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) (hb : b ∈ A ^ n) :
    MembershipSatisfies A n (existsCode φ) b ↔
      ∃ x ∈ A, MembershipSatisfies A (succ n) φ (assignmentPrepend n b x) := by
  simpa only [MembershipSatisfies, membershipSatisfactionGraph, Satisfies, membershipStructureCode_domain] using
    satisfies_exists (M := membershipStructureCode A) (e := ∅) membershipLanguageCode_valid hn hφ (by simpa using hb)

theorem directedUnion_elementary (F : V → V) (hF : ℒₛₑₜ-function₁ F) {I U : V}
    (hI : IsNonempty I) (hne : ∀ i ∈ I, IsNonempty (F i))
    (hdir : ∀ i ∈ I, ∀ j ∈ I, ∃ k ∈ I,
      IsElementaryInclusion (F i) (F k) ∧ IsElementaryInclusion (F j) (F k))
    (hunion : ∀ x, x ∈ U ↔ ∃ i ∈ I, x ∈ F i) :
    ∀ i ∈ I, IsElementaryInclusion (F i) U := by
  have hsub (i : V) (hi : i ∈ I) : F i ⊆ U := fun x hx ↦ (hunion x).mpr ⟨i, hi, hx⟩
  have hU : IsNonempty U := by
    obtain ⟨i, hi⟩ := hI.nonempty
    obtain ⟨x, hx⟩ := (hne i hi).nonempty
    exact ⟨x, hsub i hi x hx⟩
  have hmain : ∀ n φ, φ ∈ formulaSet membershipLanguageCode ∅ n → ∀ i ∈ I,
      ∀ b ∈ (F i) ^ n, MembershipSatisfies (F i) n φ b ↔ MembershipSatisfies U n φ b := by
    apply formulaSet_induction membershipLanguageCode_valid ∅
      (fun n φ ↦ ∀ i ∈ I, ∀ b ∈ (F i) ^ n,
        MembershipSatisfies (F i) n φ b ↔ MembershipSatisfies U n φ b) (by definability)
    · intro n hn
      constructor
      · intro i hi b hb
        have hbU := mem_function_of_mem_function_of_subset hb (hsub i hi)
        change Satisfies _ _ _ _ _ _ _ ↔ Satisfies _ _ _ _ _ _ _
        rw [satisfies_truth membershipLanguageCode_valid hn, satisfies_truth membershipLanguageCode_valid hn]
        exact iff_of_true (by simpa using hb) (by simpa using hbU)
      · intro i hi b hb
        exact iff_of_false (not_satisfies_falsity membershipLanguageCode_valid hn)
          (not_satisfies_falsity membershipLanguageCode_valid hn)
    · intro n hn r args ha
      constructor
      · intro i hi b hb
        have hbU := mem_function_of_mem_function_of_subset hb (hsub i hi)
        change Satisfies _ _ _ _ _ _ _ ↔ Satisfies _ _ _ _ _ _ _
        rw [satisfies_atom membershipLanguageCode_valid hn ha (by simpa using hb),
          satisfies_atom membershipLanguageCode_valid hn ha (by simpa using hbU)]
        exact membershipAtomicHolds_iff hn (hne i hi) hU hb hbU ha
      · intro i hi b hb
        have hbU := mem_function_of_mem_function_of_subset hb (hsub i hi)
        change Satisfies _ _ _ _ _ _ _ ↔ Satisfies _ _ _ _ _ _ _
        rw [satisfies_negAtom membershipLanguageCode_valid hn ha (by simpa using hb),
          satisfies_negAtom membershipLanguageCode_valid hn ha (by simpa using hbU)]
        exact not_congr (membershipAtomicHolds_iff hn (hne i hi) hU hb hbU ha)
    · intro n hn φ ψ hφ hψ ihφ ihψ
      constructor
      · intro i hi b hb
        have hbU := mem_function_of_mem_function_of_subset hb (hsub i hi)
        change Satisfies _ _ _ _ _ _ _ ↔ Satisfies _ _ _ _ _ _ _
        rw [satisfies_and membershipLanguageCode_valid hn hφ hψ (by simpa using hb),
          satisfies_and membershipLanguageCode_valid hn hφ hψ (by simpa using hbU)]
        exact and_congr (ihφ i hi b hb) (ihψ i hi b hb)
      · intro i hi b hb
        have hbU := mem_function_of_mem_function_of_subset hb (hsub i hi)
        change Satisfies _ _ _ _ _ _ _ ↔ Satisfies _ _ _ _ _ _ _
        rw [satisfies_or membershipLanguageCode_valid hn hφ hψ (by simpa using hb),
          satisfies_or membershipLanguageCode_valid hn hφ hψ (by simpa using hbU)]
        exact or_congr (ihφ i hi b hb) (ihψ i hi b hb)
    · intro n hn φ hφ ih
      have hcodes := formulaSet_quantifiers membershipLanguageCode_valid hn hφ
      constructor
      · intro i hi b hb
        have hbU := mem_function_of_mem_function_of_subset hb (hsub i hi)
        constructor
        · intro hall
          apply (membershipSatisfies_all hn hφ hbU).mpr
          intro x hx
          obtain ⟨j, hj, hxj⟩ := (hunion x).mp hx
          obtain ⟨k, hk, hik, hjk⟩ := hdir i hi j hj
          have hbk := mem_function_of_mem_function_of_subset hb hik.subset
          have hxk := hjk.subset x hxj
          have hallk := (hik.satisfaction_iff hn ((mem_formulaSet_iff _ _ _ _).mp hcodes.1) hb).mp hall
          exact (ih k hk _ (assignmentPrepend_mem_function hn hbk hxk)).mp
            ((membershipSatisfies_all hn hφ hbk).mp hallk x hxk)
        · intro hall
          apply (membershipSatisfies_all hn hφ hb).mpr
          intro x hx
          exact (ih i hi _ (assignmentPrepend_mem_function hn hb hx)).mpr
            ((membershipSatisfies_all hn hφ hbU).mp hall x (hsub i hi x hx))
      · intro i hi b hb
        have hbU := mem_function_of_mem_function_of_subset hb (hsub i hi)
        constructor
        · intro hex
          obtain ⟨x, hx, hbody⟩ := (membershipSatisfies_exists hn hφ hb).mp hex
          exact (membershipSatisfies_exists hn hφ hbU).mpr ⟨x, hsub i hi x hx,
            (ih i hi _ (assignmentPrepend_mem_function hn hb hx)).mp hbody⟩
        · intro hex
          obtain ⟨x, hx, hbody⟩ := (membershipSatisfies_exists hn hφ hbU).mp hex
          obtain ⟨j, hj, hxj⟩ := (hunion x).mp hx
          obtain ⟨k, hk, hik, hjk⟩ := hdir i hi j hj
          have hbk := mem_function_of_mem_function_of_subset hb hik.subset
          have hxk := hjk.subset x hxj
          have hbodyk := (ih k hk _ (assignmentPrepend_mem_function hn hbk hxk)).mpr hbody
          have hexk := (membershipSatisfies_exists hn hφ hbk).mpr ⟨x, hxk, hbodyk⟩
          exact (hik.satisfaction_iff hn ((mem_formulaSet_iff _ _ _ _).mp hcodes.2) hb).mpr hexk
  intro i hi
  apply IsElementaryInclusion.of_satisfaction (hne i hi) hU (hsub i hi)
  intro n _ φ hφ b hb
  exact hmain n φ ((mem_formulaSet_iff _ _ _ _).mpr hφ) i hi b hb

end ZFVP
