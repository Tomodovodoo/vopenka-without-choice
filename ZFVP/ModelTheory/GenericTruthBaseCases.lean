import ZFVP.ModelTheory.GenericInternalAtomicTruth
import ZFVP.ModelTheory.InternalGenericTruthPredicate

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

def GroundGenericTruth (A : ForcingContext V) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) (n φ : V) : Prop :=
  ∀ b : V, ∀ hb : b ∈ D ^ n,
    MembershipSatisfies (range (A.evaluationGraph D hD)) (A.check n) (A.check φ)
      (A.sequenceValue b (A.nameSequence_of_mem_function hD hb)) ↔
        GenericMeets A.G (internalForcingSet A.P A.R D n φ b)

theorem groundGenericTruth_constants (A : ForcingContext V) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) {n : V} (hn : n ∈ (ω : V)) :
    A.GroundGenericTruth D hD n truthCode ∧ A.GroundGenericTruth D hD n falsityCode := by
  have hn' : A.check n ∈ (ω : A.Model) := A.checkEmbedding.natural_iff n |>.mpr hn
  constructor
  · intro b hb
    have hb' := A.sequenceValue_mem_evaluationRange hD hb
    have ht : A.check (truthCode : V) = truthCode := A.checkEmbedding.map_truthCode
    rw [ht]
    exact iff_of_true ((satisfies_truth membershipLanguageCode_valid hn').mpr (by simpa using hb'))
      (genericMeets_internalForcing_truth A.generic.1 hn hb)
  · intro b hb
    have ht : A.check (falsityCode : V) = falsityCode := A.checkEmbedding.map_falsityCode
    rw [ht]
    exact iff_of_false (not_satisfies_falsity membershipLanguageCode_valid hn')
      (genericMeets_internalForcing_falsity hn)

theorem groundGenericTruth_atoms (A : ForcingContext V) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) {n r args : V} (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) :
    A.GroundGenericTruth D hD n (atomCode r args) ∧ A.GroundGenericTruth D hD n (negAtomCode r args) := by
  have hn' : A.check n ∈ (ω : A.Model) := A.checkEmbedding.natural_iff n |>.mpr hn
  have ham := (membershipAtomicArguments_iff hn).mp ha
  have ham' : IsMembershipAtomicArguments (A.check n) (A.check r) (A.check args) :=
    A.checkEmbedding.membershipAtomicArguments_map ham
  have ha' := (membershipAtomicArguments_iff hn').mpr ham'
  constructor
  · intro b hb
    have hb' := A.sequenceValue_mem_evaluationRange hD hb
    have ht : A.check (atomCode r args) = atomCode (A.check r) (A.check args) := A.checkEmbedding.map_atomCode r args
    rw [ht, internalForcingSet_atom hn ha hb]
    change Satisfies _ _ _ _ _ _ _ ↔ _
    rw [satisfies_atom membershipLanguageCode_valid hn' ha' (by simpa using hb'),
      ← directMembershipAtomicHolds_iff hn' hb' ham']
    exact A.genericMeets_internalAtomic hD hb ham
  · intro b hb
    have hb' := A.sequenceValue_mem_evaluationRange hD hb
    have ht : A.check (negAtomCode r args) = negAtomCode (A.check r) (A.check args) := A.checkEmbedding.map_negAtomCode r args
    rw [ht, genericMeets_internalForcing_negAtom A.order A.generic hn ha hb]
    change Satisfies _ _ _ _ _ _ _ ↔ _
    rw [satisfies_negAtom membershipLanguageCode_valid hn' ha' (by simpa using hb'),
      ← directMembershipAtomicHolds_iff hn' hb' ham']
    exact not_congr (A.genericMeets_internalAtomic hD hb ham)

end ForcingContext
end ZFVP
