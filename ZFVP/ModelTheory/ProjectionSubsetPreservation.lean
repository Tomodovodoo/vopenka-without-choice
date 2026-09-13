import ZFVP.ModelTheory.ProjectionClosedPreservation
import ZFVP.SetTheory.EndExtensionSubsetCoding

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext
variable (A B : ForcingContext V) {π E : V}
  (hπ : IsForcingSplitProjection A.P A.R B.P B.R π E)
  (he : forcingProjectionGeneric A.P A.R π B.G = A.G)

/-- A closed projection quotient adds no subsets of a set enumerated by a
short ordinal in the intermediate model. -/
theorem projectionInclusion_subset_of_separative_closed {γ X e : A.Model} [IsOrdinal γ]
    (hDC : InternalDependentChoiceAt γ)
    (hclosed : IsForcingClosedThrough (A.projectionQuotient B.P π)
      (forcingSeparativeOrder (A.projectionQuotient B.P π) (A.projectionQuotientOrder B.P B.R π)) γ)
    (henum : e ∈ X ^ γ) (hrange : range e = X)
    {Y : B.Model} (hY : Y ⊆ A.projectionInclusion B hπ he X) :
    ∃ Z, Z ⊆ X ∧ A.projectionInclusion B hπ he Z = Y := by
  apply (A.projectionInclusion B hπ he).subset_of_surjection_function_closed henum hrange
    (fun _ hf ↦ A.projectionInclusion_function_of_separative_closed B hπ he hDC hclosed hf) hY

/-- The powerset of a short enumerated set agrees across the projection inclusion. -/
theorem projectionInclusion_powerset_of_separative_closed {γ X e : A.Model} [IsOrdinal γ]
    (hDC : InternalDependentChoiceAt γ)
    (hclosed : IsForcingClosedThrough (A.projectionQuotient B.P π)
      (forcingSeparativeOrder (A.projectionQuotient B.P π) (A.projectionQuotientOrder B.P B.R π)) γ)
    (henum : e ∈ X ^ γ) (hrange : range e = X) :
    A.projectionInclusion B hπ he (℘ X) = ℘ (A.projectionInclusion B hπ he X) := by
  let j := A.projectionInclusion B hπ he
  apply mem_ext
  intro Y
  constructor
  · intro hY
    obtain ⟨Z, hZ, rfl⟩ := j.endExtension _ Y hY
    exact mem_power_iff.mpr ((j.subset_iff _ _).mpr (mem_power_iff.mp hZ))
  · intro hY
    obtain ⟨Z, hZ, rfl⟩ := A.projectionInclusion_subset_of_separative_closed B hπ he
      hDC hclosed henum hrange (mem_power_iff.mp hY)
    exact (j.mem_iff _ _).mpr (mem_power_iff.mpr hZ)

end ForcingContext
end ZFVP
