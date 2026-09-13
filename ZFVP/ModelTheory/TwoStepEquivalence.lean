import ZFVP.ModelTheory.TwoStepSecondGeneration

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TwoStepModel
variable (A : ForcingContext V) {Q S t : V} (h : IsForcingIterand A.P A.R Q S t)
  {H : Set A.Model}
  (hH : IsExternalForcingGeneric (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩) H)

theorem combinedEmbedding_surjective : Function.Surjective (combinedEmbedding A h hH) :=
  ForcingRealization.value_surjective_of_generators (iterandContext A h hH) (combinedRealization A h hH)
    (first_checks_in_range A h hH) (second_generic_in_range A h hH)

noncomputable def combinedEquiv : (combinedContext A h hH).Model ≃ (iterandContext A h hH).Model :=
  Equiv.ofBijective (combinedEmbedding A h hH)
    ⟨(combinedEmbedding A h hH).injective, combinedEmbedding_surjective A h hH⟩

theorem combinedEquiv_mem_iff (x y : (combinedContext A h hH).Model) :
    combinedEquiv A h hH x ∈ combinedEquiv A h hH y ↔ x ∈ y :=
  (combinedEmbedding A h hH).mem_iff x y

theorem combinedEquiv_check (x : V) :
    combinedEquiv A h hH ((combinedContext A h hH).check x) =
      (iterandContext A h hH).check (A.check x) :=
  (combinedRealization A h hH).value_check x

noncomputable def combinedElementaryMap :
    ElementaryMap (combinedContext A h hH).Model (iterandContext A h hH).Model :=
  ElementaryMap.ofMembershipIso (combinedEquiv A h hH) (combinedEquiv_mem_iff A h hH)

end TwoStepModel
end ZFVP
