import ZFVP.Syntax.InternalForcingTruthTables
import ZFVP.SetTheory.ForcingRegular

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem boundPairArguments_inj {i j k l : V} :
    boundPairArguments i j = boundPairArguments k l ↔ i = k ∧ j = l := by
  constructor
  · intro h
    have hv := standardTuple_injective h
    have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    exact ⟨(kpair_iff.mp h0).2, (kpair_iff.mp h1).2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem internalForcingAtomic_boundPair {n i j : V} (hi : i ∈ n) (hj : j ∈ n) (P R b r p : V) :
    InternalForcingAtomicHolds P R n b r (boundPairArguments i j) p ↔
      (((r = equalityToken ∨ r = relationToken (0 : V)) ∧ p ∈ atomicEquality P R (b ‘ i) (b ‘ j)) ∨
        (r = relationToken (1 : V) ∧ p ∈ atomicMembership P R (b ‘ i) (b ‘ j))) := by
  simp [InternalForcingAtomicHolds, hi, hj]

noncomputable def internalAtomicForcingSet (P R n b r args : V) : V :=
  {p ∈ P ; InternalForcingAtomicHolds P R n b r args p}

theorem mem_internalAtomicForcingSet (P R n b r args p : V) :
    p ∈ internalAtomicForcingSet P R n b r args ↔ p ∈ P ∧ InternalForcingAtomicHolds P R n b r args p := mem_sep_iff

theorem internalAtomicForcingSet_regular {P R n b r args : V} (hR : IsForcingPreorder P R)
    (ha : IsMembershipAtomicArguments n r args) : IsForcingRegular P R (internalAtomicForcingSet P R n b r args) := by
  have hz : (⟨(1 : V), (1 : V)⟩ₖ : V) ≠ ∅ := by
    intro h
    have hm : ({(1 : V)} : V) ∈ ⟨(1 : V), (1 : V)⟩ₖ := by simp [kpair]
    rw [h] at hm
    exact not_mem_empty hm
  obtain ⟨hr, i, hi, j, hj, rfl⟩ := ha
  rcases hr with rfl | rfl | rfl
  · have he : internalAtomicForcingSet P R n b equalityToken (boundPairArguments i j) = atomicEquality P R (b ‘ i) (b ‘ j) := by
      apply mem_ext
      intro p
      simp only [internalAtomicForcingSet, mem_sep_iff, internalForcingAtomic_boundPair hi hj]
      simp [equalityToken, relationToken, Ne.symm hz]
      exact atomicEquality_subset P R (b ‘ i) (b ‘ j) p
    rw [he]
    exact atomicEquality_regular hR _ _
  · have he : internalAtomicForcingSet P R n b (relationToken (0 : V)) (boundPairArguments i j) = atomicEquality P R (b ‘ i) (b ‘ j) := by
      apply mem_ext
      intro p
      simp only [internalAtomicForcingSet, mem_sep_iff, internalForcingAtomic_boundPair hi hj]
      simp [equalityToken, relationToken]
      exact atomicEquality_subset P R (b ‘ i) (b ‘ j) p
    rw [he]
    exact atomicEquality_regular hR _ _
  · have he : internalAtomicForcingSet P R n b (relationToken (1 : V)) (boundPairArguments i j) = atomicMembership P R (b ‘ i) (b ‘ j) := by
      apply mem_ext
      intro p
      simp only [internalAtomicForcingSet, mem_sep_iff, internalForcingAtomic_boundPair hi hj]
      simp [equalityToken, relationToken, hz]
      exact atomicMembership_subset P R (b ‘ i) (b ‘ j) p
    rw [he]
    exact atomicMembership_regular hR _ _

end ZFVP
