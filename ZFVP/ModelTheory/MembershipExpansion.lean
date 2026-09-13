import ZFVP.Syntax.MembershipLanguageExtension
import ZFVP.ModelTheory.CodedMembershipEmbedding

/-! Forgetting added symbols preserves all internally coded membership formulas. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsMembershipExpansion (L M : V) : Prop :=
  IsMembershipLanguageExtension L ∧ IsStructureCode L M ∧
    ∀ r : V, r ∈ relationSymbols (membershipLanguageCode : V) →
      (structureRelations M) ‘ r =
        (structureRelations (membershipStructureCode (structureDomain M))) ‘ r

theorem IsMembershipExpansion.atomic_iff {L M n b r args : V}
    (h : IsMembershipExpansion L M) (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) :
    AtomicHolds L ∅ M ∅ n b r args ↔ AtomicHolds membershipLanguageCode ∅
      (membershipStructureCode (structureDomain M)) ∅ n b r args := by
  rcases ha with ⟨rfl, ha⟩ | ⟨s, hs, rfl, ha⟩
  · rw [atomicHolds_equality, atomicHolds_equality,
      membershipEvaluatedArguments_extension h.1.1 hn M _ b ha]
  · rw [atomicHolds_relation, atomicHolds_relation,
      and_iff_right (h.1.2.1 s hs), and_iff_right hs,
      h.2.2 s hs, membershipEvaluatedArguments_extension h.1.1 hn M _ b ha]

theorem IsMembershipExpansion.satisfies_iff {L M n φ b : V}
    (h : IsMembershipExpansion L M) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n)
    (hb : b ∈ structureDomain M ^ n) :
    Satisfies L ∅ M ∅ n φ b ↔ Satisfies membershipLanguageCode ∅
      (membershipStructureCode (structureDomain M)) ∅ n φ b := by
  let N := membershipStructureCode (structureDomain M)
  have hd : structureDomain N = structureDomain M := membershipStructureCode_domain _
  have hsub := membershipFormulaSet_subset h.1
  apply formulaSet_induction membershipLanguageCode_valid ∅
    (fun n φ ↦ ∀ b ∈ structureDomain M ^ n,
      Satisfies L ∅ M ∅ n φ b ↔ Satisfies membershipLanguageCode ∅ N ∅ n φ b)
    (by definability) ?_ ?_ ?_ ?_ n φ hφ b hb
  · intro n hn
    constructor
    · intro b hb
      rw [satisfies_truth h.1.1 hn, satisfies_truth membershipLanguageCode_valid hn, hd]
    · intro b _
      exact iff_of_false (not_satisfies_falsity h.1.1 hn)
        (not_satisfies_falsity membershipLanguageCode_valid hn)
  · intro n hn r args ha
    have haL := membershipAtomicArguments_extension h.1 hn ha
    constructor
    · intro b hb
      have hbN : b ∈ structureDomain N ^ n := by rwa [hd]
      rw [satisfies_atom h.1.1 hn haL hb, satisfies_atom membershipLanguageCode_valid hn ha hbN]
      exact h.atomic_iff hn ha
    · intro b hb
      have hbN : b ∈ structureDomain N ^ n := by rwa [hd]
      rw [satisfies_negAtom h.1.1 hn haL hb, satisfies_negAtom membershipLanguageCode_valid hn ha hbN]
      exact not_congr (h.atomic_iff hn ha)
  · intro n hn φ ψ hφ hψ ihφ ihψ
    constructor
    · intro b hb
      have hbN : b ∈ structureDomain N ^ n := by rwa [hd]
      rw [satisfies_and h.1.1 hn (hsub n φ hφ) (hsub n ψ hψ) hb,
        satisfies_and membershipLanguageCode_valid hn hφ hψ hbN, ihφ b hb, ihψ b hb]
    · intro b hb
      have hbN : b ∈ structureDomain N ^ n := by rwa [hd]
      rw [satisfies_or h.1.1 hn (hsub n φ hφ) (hsub n ψ hψ) hb,
        satisfies_or membershipLanguageCode_valid hn hφ hψ hbN, ihφ b hb, ihψ b hb]
  · intro n hn φ hφ ih
    constructor
    · intro b hb
      have hbN : b ∈ structureDomain N ^ n := by rwa [hd]
      rw [satisfies_all h.1.1 hn (hsub (succ n) φ hφ) hb,
        satisfies_all membershipLanguageCode_valid hn hφ hbN, hd]
      apply forall_congr'
      intro x
      apply imp_congr_right
      intro hx
      exact ih _ (assignmentPrepend_mem_function hn hb hx)
    · intro b hb
      have hbN : b ∈ structureDomain N ^ n := by rwa [hd]
      rw [satisfies_exists h.1.1 hn (hsub (succ n) φ hφ) hb,
        satisfies_exists membershipLanguageCode_valid hn hφ hbN, hd]
      apply exists_congr
      intro x
      apply and_congr_right
      intro hx
      exact ih _ (assignmentPrepend_mem_function hn hb hx)

theorem IsCodedElementaryEmbedding.membership_reduct {L M N f : V}
    (h : IsCodedElementaryEmbedding L M N f)
    (hM : IsMembershipExpansion L M) (hN : IsMembershipExpansion L N) :
    IsCodedMembershipEmbedding (structureDomain M) (structureDomain N) f := by
  refine ⟨membershipStructureCode_valid h.source.domain_nonempty,
    membershipStructureCode_valid h.target.domain_nonempty, ?_, ?_⟩
  · simpa only [membershipStructureCode_domain] using h.function
  · intro n hn φ hφ b hb
    simp only [membershipStructureCode_domain] at hb
    exact (hM.satisfies_iff hφ hb).symm.trans
      ((h.satisfies_iff hn (membershipFormulaSet_subset hM.1 n φ hφ) hb).trans
        (hN.satisfies_iff hφ (compose_function hb h.function)))

end ZFVP
