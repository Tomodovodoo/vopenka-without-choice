import ZFVP.Syntax.EndExtensionSatisfaction
import ZFVP.Syntax.EndExtensionMembershipSyntax

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_equalityRelation (j : MembershipEndExtension V W) (A : V) :
    j (equalityRelation A) = equalityRelation (j A) := by
  have hh := j.map_separation (A ^ (2 : V)) (fun s ↦ s ‘ (0 : V) = s ‘ (1 : V))
    (fun s ↦ s ‘ (0 : W) = s ‘ (1 : W)) (by definability) (by definability) (by
      intro s _
      rw [← show j (0 : V) = (0 : W) from j.map_numeral 0, ← show j (1 : V) = (1 : W) from j.map_numeral 1, ← j.map_value_total, ← j.map_value_total]
      exact j.injective.eq_iff.symm)
  simpa only [equalityRelation, j.map_finiteFunctionSet A (show (2 : V) ∈ (ω : V) by simp),
    show j (2 : V) = (2 : W) from j.map_numeral 2] using hh

theorem map_membershipTupleRelation (j : MembershipEndExtension V W) (A : V) :
    j (membershipTupleRelation A) = membershipTupleRelation (j A) := by
  have hh := j.map_separation (A ^ (2 : V)) (fun s ↦ s ‘ (0 : V) ∈ s ‘ (1 : V))
    (fun s ↦ s ‘ (0 : W) ∈ s ‘ (1 : W)) (by definability) (by definability) (by
      intro s _
      rw [← show j (0 : V) = (0 : W) from j.map_numeral 0, ← show j (1 : V) = (1 : W) from j.map_numeral 1, ← j.map_value_total, ← j.map_value_total]
      exact (j.mem_iff _ _).symm)
  simpa only [membershipTupleRelation, j.map_finiteFunctionSet A (show (2 : V) ∈ (ω : V) by simp),
    show j (2 : V) = (2 : W) from j.map_numeral 2] using hh

theorem map_membershipInterpretation (j : MembershipEndExtension V W) (A r : V) :
    j (membershipInterpretation A r) = membershipInterpretation (j A) (j r) := by
  have hz : j r = (0 : W) ↔ r = (0 : V) := by
    rw [← show j (0 : V) = (0 : W) from j.map_numeral 0, j.injective.eq_iff]
  unfold membershipInterpretation
  by_cases hr : r = 0
  · rw [ite_eq_left hr, ite_eq_left (hz.mpr hr)]
    exact j.map_equalityRelation A
  · rw [ite_eq_right hr, ite_eq_right ((not_congr hz).mpr hr)]
    exact j.map_membershipTupleRelation A

theorem map_membershipStructureCode (j : MembershipEndExtension V W) (A : V) :
    j (membershipStructureCode A) = membershipStructureCode (j A) := by
  have hh := j.map_definableGraph (2 : V) (membershipInterpretation A) (membershipInterpretation (j A))
    (by definability) (by definability) (fun r _ ↦ j.map_membershipInterpretation A r)
  unfold membershipStructureCode structureCode
  rw [j.map_kpair, j.map_kpair, j.map_constantGraph, j.map_empty, hh,
    show j (2 : V) = (2 : W) from j.map_numeral 2]

theorem membershipSatisfies_iff (j : MembershipEndExtension V W) (A n φ b : V) :
    MembershipSatisfies (j A) (j n) (j φ) (j b) ↔ MembershipSatisfies A n φ b := by
  have hh := j.satisfies_iff membershipLanguageCode_valid ∅ (membershipStructureCode A) ∅ n φ b
  rw [j.map_membershipLanguageCode, j.map_empty, j.map_membershipStructureCode] at hh
  exact hh

end MembershipEndExtension
end ZFVP
