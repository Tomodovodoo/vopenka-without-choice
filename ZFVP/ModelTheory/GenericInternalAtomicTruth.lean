import ZFVP.ModelTheory.ForcingAssignmentDomain
import ZFVP.Syntax.EndExtensionMembershipSyntax
import ZFVP.Syntax.InternalAtomicForcingRegular

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem directMembershipAtomic_boundPair {n i j : V} (hi : i ∈ n) (hj : j ∈ n) (b r : V) :
    DirectMembershipAtomicHolds n b r (boundPairArguments i j) ↔
      (((r = equalityToken ∨ r = relationToken (0 : V)) ∧ b ‘ i = b ‘ j) ∨
        (r = relationToken (1 : V) ∧ b ‘ i ∈ b ‘ j)) := by
  simp [DirectMembershipAtomicHolds, hi, hj]

namespace ForcingContext

theorem genericMeets_internalAtomic (A : ForcingContext V) {D n b r args : V}
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) (hb : b ∈ D ^ n)
    (ha : IsMembershipAtomicArguments n r args) :
    DirectMembershipAtomicHolds (A.check n)
      (A.sequenceValue b (A.nameSequence_of_mem_function hD hb)) (A.check r) (A.check args) ↔
      GenericMeets A.G (internalAtomicForcingSet A.P A.R n b r args) := by
  obtain ⟨hr, i, hi, j, hj, rfl⟩ := ha
  have hi' := (A.check_mem_iff i n).mpr hi
  have hj' := (A.check_mem_iff j n).mpr hj
  have hid : i ∈ domain b := domain_eq_of_mem_function hb ▸ hi
  have hjd : j ∈ domain b := domain_eq_of_mem_function hb ▸ hj
  rw [show A.check (boundPairArguments i j) = boundPairArguments (A.check i) (A.check j) from A.checkEmbedding.map_boundPairArguments i j, directMembershipAtomic_boundPair hi' hj',
    A.sequenceValue_value _ _ hid, A.sequenceValue_value _ _ hjd]
  have heq := forcingQuotientMk_eq_iff A.P A.R A.G A.order A.generic.1
    ⟨b ‘ i, hD _ (function_value_mem hb hi)⟩ ⟨b ‘ j, hD _ (function_value_mem hb hj)⟩
  have hmem := forcingQuotientMk_mem_iff A.P A.R A.G A.order A.generic.1
    ⟨b ‘ i, hD _ (function_value_mem hb hi)⟩ ⟨b ‘ j, hD _ (function_value_mem hb hj)⟩
  change _ ↔ ∃ p ∈ A.G, p ∈ internalAtomicForcingSet A.P A.R n b r (boundPairArguments i j)
  simp only [mem_internalAtomicForcingSet, internalForcingAtomic_boundPair hi hj]
  have hzero : A.check r = equalityToken ↔ r = equalityToken := by
    rw [← A.checkEmbedding.map_equalityToken]
    exact A.check_eq_iff _ _
  have hrel (k : ℕ) : A.check r = relationToken (k : A.Model) ↔ r = relationToken (k : V) := by
    rw [← A.checkEmbedding.map_numeral k, ← A.checkEmbedding.map_relationToken]
    exact A.check_eq_iff _ _
  have hrel0 : A.check r = relationToken (0 : A.Model) ↔ r = relationToken (0 : V) := by simpa using hrel 0
  have hrel1 : A.check r = relationToken (1 : A.Model) ↔ r = relationToken (1 : V) := by simpa using hrel 1
  rw [hzero, hrel0, hrel1]
  change (((r = equalityToken ∨ r = relationToken (0 : V)) ∧
      A.ofName _ = A.ofName _) ∨ (r = relationToken (1 : V) ∧ A.ofName _ ∈ A.ofName _)) ↔ _
  have heq' : A.ofName ⟨b ‘ i, hD _ (function_value_mem hb hi)⟩ = A.ofName ⟨b ‘ j, hD _ (function_value_mem hb hj)⟩ ↔ GenericMeets A.G (atomicEquality A.P A.R (b ‘ i) (b ‘ j)) := heq
  have hmem' : A.ofName ⟨b ‘ i, hD _ (function_value_mem hb hi)⟩ ∈ A.ofName ⟨b ‘ j, hD _ (function_value_mem hb hj)⟩ ↔ GenericMeets A.G (atomicMembership A.P A.R (b ‘ i) (b ‘ j)) := hmem
  rw [heq', hmem']
  constructor
  · rintro (⟨hr, p, hp, he⟩ | ⟨hr, p, hp, hm⟩)
    · exact ⟨p, hp, A.generic.1.1 p hp, Or.inl ⟨hr, he⟩⟩
    · exact ⟨p, hp, A.generic.1.1 p hp, Or.inr ⟨hr, hm⟩⟩
  · rintro ⟨p, hp, _, h⟩
    rcases h with ⟨hr, he⟩ | ⟨hr, hm⟩
    · exact Or.inl ⟨hr, p, hp, he⟩
    · exact Or.inr ⟨hr, p, hp, hm⟩

end ForcingContext
end ZFVP
