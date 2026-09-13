import ZFVP.ModelTheory.ForcingClosedSequences
import ZFVP.SetTheory.EndExtensionHierarchyAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Closed forcing preserves a rank whose earlier levels have short enumerations. -/
theorem ForcingContext.check_hierarchy_of_closed (A : ForcingContext V) {θ κ : V}
    [IsOrdinal θ] [IsOrdinal κ]
    (hDC : ∀ γ ∈ κ, InternalDependentChoiceAt γ)
    (hclosed : IsForcingClosedBelow A.P A.R κ)
    (henum : ∀ α ∈ θ, ∃ γ ∈ κ, ∃ e ∈ (hierarchy α) ^ γ, range e = hierarchy α) :
    A.check (hierarchy θ) = hierarchy (A.check θ) := by
  apply A.checkEmbedding.map_hierarchy_of_power_agreement
  intro α hα
  obtain ⟨γ, hγκ, e, he, hr⟩ := henum α hα
  let := IsOrdinal.of_mem hγκ
  apply A.checkEmbedding.map_power_of_surjection_function_closed he hr
  intro f hf
  apply A.function_eq_check_of_closed (hDC γ hγκ) ?_ hf
  intro β hβ hβγ
  let := hβ
  exact hclosed β (ordinal_mem_of_subset_mem hβγ hγκ)

end ZFVP
