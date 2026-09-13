import ZFVP.ModelTheory.BinaryRelationStructure
import ZFVP.ModelTheory.EndExtensionCodedEmbedding

/-! Binary structure codes and their actual coded elementary embeddings
are preserved by membership end extensions of ambient ZF models. -/

set_option autoImplicit false

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_binaryTupleRelation (j : MembershipEndExtension V W) (D E : V) :
    j (binaryTupleRelation D E) = binaryTupleRelation (j D) (j E) := by
  have hh := j.map_separation (D ^ (2 : V))
    (fun s ↦ ⟨s ‘ (0 : V), s ‘ (1 : V)⟩ₖ ∈ E)
    (fun s ↦ ⟨s ‘ (0 : W), s ‘ (1 : W)⟩ₖ ∈ j E)
    (by definability) (by definability) (by
      intro s _
      rw [← show j (0 : V) = (0 : W) from j.map_numeral 0,
        ← show j (1 : V) = (1 : W) from j.map_numeral 1,
        ← j.map_value_total, ← j.map_value_total, ← j.map_kpair]
      exact (j.mem_iff _ _).symm)
  simpa only [binaryTupleRelation, j.map_finiteFunctionSet D (show (2 : V) ∈ (ω : V) by simp),
    show j (2 : V) = (2 : W) from j.map_numeral 2] using hh

theorem map_binaryRelationInterpretation (j : MembershipEndExtension V W) (D E r : V) :
    j (binaryRelationInterpretation D E r) = binaryRelationInterpretation (j D) (j E) (j r) := by
  have hz : j r = (0 : W) ↔ r = (0 : V) := by
    rw [← show j (0 : V) = (0 : W) from j.map_numeral 0, j.injective.eq_iff]
  unfold binaryRelationInterpretation
  by_cases hr : r = 0
  · rw [ite_eq_left hr, ite_eq_left (hz.mpr hr)]
    exact j.map_equalityRelation D
  · rw [ite_eq_right hr, ite_eq_right ((not_congr hz).mpr hr)]
    exact j.map_binaryTupleRelation D E

theorem map_binaryRelationStructureCode (j : MembershipEndExtension V W) (D E : V) :
    j (binaryRelationStructureCode D E) = binaryRelationStructureCode (j D) (j E) := by
  have hh := j.map_definableGraph (2 : V) (binaryRelationInterpretation D E)
    (binaryRelationInterpretation (j D) (j E)) (by definability) (by definability)
    (fun r _ ↦ j.map_binaryRelationInterpretation D E r)
  unfold binaryRelationStructureCode
  rw [j.map_structureCode, j.map_constantGraph, j.map_empty, hh,
    show j (2 : V) = (2 : W) from j.map_numeral 2]

theorem codedBinaryElementaryEmbedding_iff (j : MembershipEndExtension V W) (D E B R f : V) :
    IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode (j D) (j E))
      (binaryRelationStructureCode (j B) (j R)) (j f) ↔
    IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode D E)
      (binaryRelationStructureCode B R) f := by
  simpa only [j.map_membershipLanguageCode, j.map_binaryRelationStructureCode] using
    j.codedElementaryEmbedding_iff membershipLanguageCode (binaryRelationStructureCode D E)
      (binaryRelationStructureCode B R) f

theorem map_codedBinaryElementaryEmbedding (j : MembershipEndExtension V W) {D E B R f : V}
    (hf : IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode D E)
      (binaryRelationStructureCode B R) f) :
    IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode (j D) (j E))
      (binaryRelationStructureCode (j B) (j R)) (j f) :=
  (j.codedBinaryElementaryEmbedding_iff D E B R f).mpr hf

end MembershipEndExtension
end ZFVP
