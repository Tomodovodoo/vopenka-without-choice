import ZFVP.Syntax.MembershipAtomicSemantics
import ZFVP.SetTheory.LevelOneTruth

/-! Absoluteness for every internal bounded formula code. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem membershipSatisfies_boundedAll {A n i φ b : V} [hA : IsTransitive A]
    (hn : n ∈ (ω : V)) (hi : i ∈ n) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n))
    (hb : b ∈ A ^ n) :
    MembershipSatisfies A n (boundedAllCode i φ) b ↔
      ∀ x ∈ b ‘ i, MembershipSatisfies A (succ n) φ (assignmentPrepend n b x) := by
  have hg := boundedGuardArguments_valid hn hi
  have hgφ := (formulaSet_atoms membershipLanguageCode_valid (ω_succ_closed hn) hg).2
  have hb' : b ∈ structureDomain (membershipStructureCode A) ^ n := by simpa using hb
  change Satisfies membershipLanguageCode ∅ (membershipStructureCode A) ∅ n _ b ↔ _
  rw [boundedAllCode, satisfies_all membershipLanguageCode_valid hn
    (formulaSet_binary membershipLanguageCode_valid (ω_succ_closed hn) hgφ hφ).2 hb']
  simp only [membershipStructureCode_domain]
  have hstep (x : V) (hx : x ∈ A) :
      Satisfies membershipLanguageCode ∅ (membershipStructureCode A) ∅ (succ n)
        (orCode (negAtomCode (relationToken (1 : V)) (boundedGuardArguments i)) φ)
        (assignmentPrepend n b x) ↔
      (x ∈ b ‘ i → MembershipSatisfies A (succ n) φ (assignmentPrepend n b x)) := by
    have hbx : assignmentPrepend n b x ∈ structureDomain (membershipStructureCode A) ^ succ n := by
      simpa using assignmentPrepend_mem_function hn hb hx
    rw [satisfies_or membershipLanguageCode_valid (ω_succ_closed hn) hgφ hφ hbx,
      satisfies_negAtom membershipLanguageCode_valid (ω_succ_closed hn) hg hbx,
      membershipGuard_atomicHolds hn hi hb hx]
    simp only [or_iff_not_imp_left, not_not]
    rfl
  constructor
  · intro h x hx
    have hxA := hA.transitive _ (function_value_mem hb hi) x hx
    exact (hstep x hxA).mp (h x hxA) hx
  · intro h x hx
    exact (hstep x hx).mpr (h x)

theorem membershipSatisfies_boundedExists {A n i φ b : V} [hA : IsTransitive A]
    (hn : n ∈ (ω : V)) (hi : i ∈ n) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n))
    (hb : b ∈ A ^ n) :
    MembershipSatisfies A n (boundedExistsCode i φ) b ↔
      ∃ x ∈ b ‘ i, MembershipSatisfies A (succ n) φ (assignmentPrepend n b x) := by
  have hg := boundedGuardArguments_valid hn hi
  have hgφ := (formulaSet_atoms membershipLanguageCode_valid (ω_succ_closed hn) hg).1
  have hb' : b ∈ structureDomain (membershipStructureCode A) ^ n := by simpa using hb
  change Satisfies membershipLanguageCode ∅ (membershipStructureCode A) ∅ n _ b ↔ _
  rw [boundedExistsCode, satisfies_exists membershipLanguageCode_valid hn
    (formulaSet_binary membershipLanguageCode_valid (ω_succ_closed hn) hgφ hφ).1 hb']
  simp only [membershipStructureCode_domain]
  have hstep (x : V) (hx : x ∈ A) :
      Satisfies membershipLanguageCode ∅ (membershipStructureCode A) ∅ (succ n)
        (andCode (atomCode (relationToken (1 : V)) (boundedGuardArguments i)) φ)
        (assignmentPrepend n b x) ↔
      (x ∈ b ‘ i ∧ MembershipSatisfies A (succ n) φ (assignmentPrepend n b x)) := by
    have hbx : assignmentPrepend n b x ∈ structureDomain (membershipStructureCode A) ^ succ n := by
      simpa using assignmentPrepend_mem_function hn hb hx
    rw [satisfies_and membershipLanguageCode_valid (ω_succ_closed hn) hgφ hφ hbx,
      satisfies_atom membershipLanguageCode_valid (ω_succ_closed hn) hg hbx,
      membershipGuard_atomicHolds hn hi hb hx]
    rfl
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, (hstep x hx).mp h⟩
  · rintro ⟨x, hx, h⟩
    have hxA := hA.transitive _ (function_value_mem hb hi) x hx
    exact ⟨x, hxA, (hstep x hxA).mpr ⟨hx, h⟩⟩

def MembershipSatisfactionAbsolute (n φ : V) : Prop :=
  ∀ A B : V, IsTransitive A → IsTransitive B → IsNonempty A → IsNonempty B →
    ∀ b, b ∈ A ^ n → b ∈ B ^ n → (MembershipSatisfies A n φ b ↔ MembershipSatisfies B n φ b)

instance membershipSatisfactionAbsolute_definable : ℒₛₑₜ-relation[V] MembershipSatisfactionAbsolute := by
  unfold MembershipSatisfactionAbsolute
  definability

theorem boundedFormulaCode_absolute {n φ : V} (hφ : IsBoundedFormulaCode n φ) :
    MembershipSatisfactionAbsolute n φ := by
  suffices h : ∀ p ∈ (boundedFormulaFamily : V),
      MembershipSatisfactionAbsolute (kpair.π₁ p) (kpair.π₂ p) by
    simpa using h ⟨n, φ⟩ₖ hφ
  refine boundedFormulaFamily_induction
    (fun p : V ↦ MembershipSatisfactionAbsolute (kpair.π₁ p) (kpair.π₂ p)) (by definability) ?_ ?_ ?_ ?_
  all_goals simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  · intro n hn
    constructor
    · intro A B _ _ _ _ b hbA hbB
      change Satisfies _ _ _ _ _ _ _ ↔ Satisfies _ _ _ _ _ _ _
      rw [satisfies_truth membershipLanguageCode_valid hn, satisfies_truth membershipLanguageCode_valid hn]
      exact iff_of_true (by simpa using hbA) (by simpa using hbB)
    · intro A B _ _ _ _ b _ _
      exact iff_of_false (not_satisfies_falsity membershipLanguageCode_valid hn)
        (not_satisfies_falsity membershipLanguageCode_valid hn)
  · intro n hn r args ha
    constructor
    · intro A B _ _ hA hB b hbA hbB
      change Satisfies _ _ _ _ _ _ _ ↔ Satisfies _ _ _ _ _ _ _
      rw [satisfies_atom membershipLanguageCode_valid hn ha (by simpa using hbA),
        satisfies_atom membershipLanguageCode_valid hn ha (by simpa using hbB)]
      exact membershipAtomicHolds_iff hn hA hB hbA hbB ha
    · intro A B _ _ hA hB b hbA hbB
      change Satisfies _ _ _ _ _ _ _ ↔ Satisfies _ _ _ _ _ _ _
      rw [satisfies_negAtom membershipLanguageCode_valid hn ha (by simpa using hbA),
        satisfies_negAtom membershipLanguageCode_valid hn ha (by simpa using hbB)]
      exact not_congr (membershipAtomicHolds_iff hn hA hB hbA hbB ha)
  · intro n hn φ ψ hφ hψ ihφ ihψ
    have hvφ := IsBoundedFormulaCode.valid hφ
    have hvψ := IsBoundedFormulaCode.valid hψ
    constructor
    · intro A B hAt hBt hA hB b hbA hbB
      change Satisfies _ _ _ _ _ _ _ ↔ Satisfies _ _ _ _ _ _ _
      rw [satisfies_and membershipLanguageCode_valid hn hvφ hvψ (by simpa using hbA),
        satisfies_and membershipLanguageCode_valid hn hvφ hvψ (by simpa using hbB)]
      exact and_congr (ihφ A B hAt hBt hA hB b hbA hbB) (ihψ A B hAt hBt hA hB b hbA hbB)
    · intro A B hAt hBt hA hB b hbA hbB
      change Satisfies _ _ _ _ _ _ _ ↔ Satisfies _ _ _ _ _ _ _
      rw [satisfies_or membershipLanguageCode_valid hn hvφ hvψ (by simpa using hbA),
        satisfies_or membershipLanguageCode_valid hn hvφ hvψ (by simpa using hbB)]
      exact or_congr (ihφ A B hAt hBt hA hB b hbA hbB) (ihψ A B hAt hBt hA hB b hbA hbB)
  · intro n hn i hi φ hφ ih
    have hvφ := IsBoundedFormulaCode.valid hφ
    constructor
    · intro A B hAt hBt hA hB b hbA hbB
      let := hAt
      let := hBt
      rw [membershipSatisfies_boundedAll hn hi hvφ hbA, membershipSatisfies_boundedAll hn hi hvφ hbB]
      apply forall_congr'
      intro x
      apply forall_congr'
      intro hx
      exact ih A B hAt hBt hA hB _
        (assignmentPrepend_mem_function hn hbA (hAt.transitive _ (function_value_mem hbA hi) x hx))
        (assignmentPrepend_mem_function hn hbB (hBt.transitive _ (function_value_mem hbB hi) x hx))
    · intro A B hAt hBt hA hB b hbA hbB
      let := hAt
      let := hBt
      rw [membershipSatisfies_boundedExists hn hi hvφ hbA, membershipSatisfies_boundedExists hn hi hvφ hbB]
      apply exists_congr
      intro x
      apply and_congr_right
      intro hx
      exact ih A B hAt hBt hA hB _
        (assignmentPrepend_mem_function hn hbA (hAt.transitive _ (function_value_mem hbA hi) x hx))
        (assignmentPrepend_mem_function hn hbB (hBt.transitive _ (function_value_mem hbB hi) x hx))

theorem membershipSatisfies_bounded_absolute {A B n φ b : V} [hAt : IsTransitive A] [hBt : IsTransitive B]
    (hφ : IsBoundedFormulaCode n φ) (hA : IsNonempty A) (hB : IsNonempty B)
    (hbA : b ∈ A ^ n) (hbB : b ∈ B ^ n) :
    MembershipSatisfies A n φ b ↔ MembershipSatisfies B n φ b :=
  boundedFormulaCode_absolute hφ A B hAt hBt hA hB b hbA hbB

theorem assignment_mem_boundedTruthDomain {n b : V} [IsFunction b] (hb : domain b = n) :
    b ∈ boundedTruthDomain b ^ n := by
  rw [← hb]
  exact mem_function_of_mem_function_of_subset (IsFunction.mem_function b) (range_subset_boundedTruthDomain b)

theorem boundedTruth_iff_membershipSatisfies {A n φ b : V} [IsTransitive A]
    (hφ : IsBoundedFormulaCode n φ) (hA : IsNonempty A) (hb : b ∈ A ^ n) :
    BoundedTruth n φ b ↔ MembershipSatisfies A n φ b := by
  have : IsFunction b := IsFunction.of_mem hb
  exact membershipSatisfies_bounded_absolute hφ (boundedTruthDomain_nonempty b) hA
    (assignment_mem_boundedTruthDomain (domain_eq_of_mem_function hb)) hb

theorem sigmaOneTruth_bounded_iff {n φ b : V} [IsFunction b]
    (hφ : IsBoundedFormulaCode n φ) (hb : domain b = n) :
    SigmaOneTruth n φ b ↔ BoundedTruth n φ b := by
  constructor
  · rintro ⟨A, hAt, hA, hbA, hs⟩
    let := hAt
    exact (boundedTruth_iff_membershipSatisfies hφ hA hbA).mpr hs
  · intro hs
    exact ⟨boundedTruthDomain b, inferInstance, boundedTruthDomain_nonempty b,
      assignment_mem_boundedTruthDomain hb, hs⟩

theorem piOneTruth_bounded_iff {n φ b : V} [IsFunction b]
    (hφ : IsBoundedFormulaCode n φ) (hb : domain b = n) :
    PiOneTruth n φ b ↔ BoundedTruth n φ b := by
  constructor
  · intro hs
    exact hs (boundedTruthDomain b) inferInstance (boundedTruthDomain_nonempty b)
      (assignment_mem_boundedTruthDomain hb)
  · intro hs A hAt hA hbA
    let := hAt
    exact (boundedTruth_iff_membershipSatisfies hφ hA hbA).mp hs

end ZFVP
