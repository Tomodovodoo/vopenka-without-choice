import ZFVP.ModelTheory.FiniteRankLiftDomain
import ZFVP.ModelTheory.EndExtensionRankMembership

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace FiniteRankLiftData
variable {A B : ForcingContext V} {δ ε e π : V} (L : FiniteRankLiftData A B δ ε e)
  (hπ : IsForcingRetraction A.P A.R B.P B.R π)

theorem graph_subset_rank_product :
    L.graph hπ ⊆ hierarchy (B.check δ) ×ˢ hierarchy (B.check ε) := by
  let := L.source_inaccessible.1
  let := L.target_inaccessible.1
  intro z hz
  obtain ⟨τ, hτ, rfl⟩ := (B.mem_mapGraph_iff L.nameDomain e (L.graphName_isName hπ)
    (fun _ hσ ↦ (L.nameDomain_name hσ).mono hπ.inclusion)
    (fun _ hσ ↦ L.image_name (L.nameDomain_rank hσ) (L.nameDomain_name hσ)) z).mp hz
  exact kpair_mem_iff.mpr
    ⟨B.ofName_mem_checked_hierarchy _ (L.nameDomain_rank hτ),
      B.ofName_mem_checked_hierarchy _ (L.imageName_rank ⟨τ, L.nameDomain_name hτ⟩ (L.nameDomain_rank hτ))⟩

/-- The lift graph itself belongs to every larger limit rank containing the two
marked heights. This is stronger than merely constructing it in the full generic extension. -/
theorem graph_mem_larger_rank {Ω : V} [IsOrdinal Ω]
    (hΩ : ∀ β ∈ Ω, succ β ∈ Ω) (hδ : δ ∈ Ω) (hε : ε ∈ Ω) :
    L.graph hπ ∈ hierarchy (B.check Ω) := by
  let := L.source_inaccessible.1
  let := L.target_inaccessible.1
  have hs : ∀ β ∈ B.check Ω, succ β ∈ B.check Ω := by
    intro β hβ
    obtain ⟨a, ha, rfl⟩ := (B.mem_check_iff Ω β).mp hβ
    rw [← B.check_succ]
    exact (B.check_mem_iff _ _).mpr (hΩ a ha)
  exact subset_mem_hierarchy_limit hs
    (prod_mem_hierarchy_limit hs
      (hierarchy_mem ((B.check_mem_iff _ _).mpr hδ))
      (hierarchy_mem ((B.check_mem_iff _ _).mpr hε)))
    (L.graph_subset_rank_product hπ)

theorem graph_mem_larger_rank_in_extension {Ω : V} [IsOrdinal Ω]
    (hΩ : ∀ β ∈ Ω, succ β ∈ Ω) (hδ : δ ∈ Ω) (hε : ε ∈ Ω)
    {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (j : MembershipEndExtension B.Model W) :
    j (L.graph hπ) ∈ hierarchy (j (B.check Ω)) :=
  (j.mem_mapped_hierarchy_iff _ _).mpr (L.graph_mem_larger_rank hπ hΩ hδ hε)

end FiniteRankLiftData
end ZFVP
