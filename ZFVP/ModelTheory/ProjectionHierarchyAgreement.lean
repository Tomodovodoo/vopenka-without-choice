import ZFVP.ModelTheory.ProjectionSubsetPreservation
import ZFVP.SetTheory.EndExtensionHierarchyAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext
variable (A B : ForcingContext V) {π E : V}
  (hπ : IsForcingSplitProjection A.P A.R B.P B.R π E)
  (he : forcingProjectionGeneric A.P A.R π B.G = A.G)

/-- Short enumerations of the earlier ranks and closed tails give rank agreement. -/
theorem projectionInclusion_hierarchy_of_separative_closed {κ η : A.Model}
    [IsOrdinal κ] [IsOrdinal η]
    (hDC : ∀ γ ∈ η, InternalDependentChoiceAt γ)
    (hclosed : IsForcingClosedBelow (A.projectionQuotient B.P π)
      (forcingSeparativeOrder (A.projectionQuotient B.P π) (A.projectionQuotientOrder B.P B.R π)) η)
    (henum : ∀ α ∈ κ, ∃ γ ∈ η, ∃ e ∈ (hierarchy α) ^ γ, range e = hierarchy α) :
    A.projectionInclusion B hπ he (hierarchy κ) = hierarchy (A.projectionInclusion B hπ he κ) := by
  apply (A.projectionInclusion B hπ he).map_hierarchy_of_power_agreement
  intro α hα
  obtain ⟨γ, hγη, e, heγ, her⟩ := henum α hα
  let := IsOrdinal.of_mem hγη
  apply A.projectionInclusion_powerset_of_separative_closed B hπ he (hDC γ hγη) ?_ heγ her
  intro β hβ hβγ
  let := hβ
  exact hclosed β (ordinal_mem_of_subset_mem hβγ hγη)

end ForcingContext
end ZFVP
