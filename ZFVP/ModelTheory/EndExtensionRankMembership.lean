import ZFVP.SetTheory.EndExtensionRank
import ZFVP.SetTheory.EndExtensionHierarchyAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- An old set has the same rank in an end extension, even when the extension
has new sets in that rank. -/
theorem mem_mapped_hierarchy_iff (j : MembershipEndExtension V W) (x κ : V) [IsOrdinal κ] :
    j x ∈ hierarchy (j κ) ↔ x ∈ hierarchy κ := by
  let := (j.ordinal_iff κ).mpr inferInstance
  rw [mem_hierarchy_iff_rank_mem, mem_hierarchy_iff_rank_mem, ← j.map_rank, j.mem_iff]

end MembershipEndExtension
end ZFVP
