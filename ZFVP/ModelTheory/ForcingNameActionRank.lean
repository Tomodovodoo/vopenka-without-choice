import ZFVP.ModelTheory.ProjectionNameTransport
import ZFVP.SetTheory.EndExtensionRank
import ZFVP.SetTheory.NameValueRank
import ZFVP.ModelTheory.TransitiveZFNames
import ZFVP.SetTheory.ChoicelessInaccessibleRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameValue_nameAction_rank_subset {P π G τ : V} (hτ : IsForcingName P τ) :
    rank (nameValue G (nameAction π τ)) ⊆ rank τ := by
  let H := {p ∈ P ; π ‘ p ∈ G}
  have he : nameValue G (nameAction π τ) = nameValue H τ :=
    nameValue_nameAction_of_membership hτ (fun p hp ↦ by simp [H, hp])
  rw [he]
  exact rank_nameValue_subset H τ

/-- Recoding conditions does not increase the rank of the interpreted name,
even when the new conditions themselves have large set rank. -/
theorem ForcingContext.ofName_nameAction_mem_hierarchy (B : ForcingContext V)
    {P π τ δ : V} [IsOrdinal δ] (hπ : π ∈ B.P ^ P)
    (hτ : IsForcingName P τ) (hτδ : τ ∈ hierarchy δ) :
    B.ofName ⟨nameAction π τ, nameAction_isName hπ hτ⟩ ∈ hierarchy (B.check δ) := by
  rw [← B.nameValue_genericSet_check]
  rw [show B.check (nameAction π τ) = nameAction (B.check π) (B.check τ)
    from B.checkEmbedding.map_nameAction π τ]
  have hb := nameValue_nameAction_rank_subset
    ((B.checkEmbedding.forcingName_iff P τ).mp hτ) (π := B.check π) (G := B.genericSet)
  rw [← B.checkEmbedding.map_rank τ] at hb
  let : IsOrdinal (B.checkEmbedding (rank τ)) := by
    change IsOrdinal (B.check (rank τ))
    infer_instance
  apply (mem_hierarchy_iff_rank_mem _ _).mpr
  have ht := (B.check_mem_iff _ _).mpr ((mem_hierarchy_iff_rank_mem τ δ).mp hτδ)
  rcases IsOrdinal.subset_iff.mp hb with he | hm
  · exact he.symm ▸ ht
  · exact IsOrdinal.toIsTransitive.mem_trans hm ht

theorem nameAction_mem_hierarchy_of_inaccessible {δ P π τ : V}
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hπ : π ∈ hierarchy δ)
    (hτ : τ ∈ hierarchy δ) (hn : IsForcingName P τ) : nameAction π τ ∈ hierarchy δ := by
  let := hδ.1
  let := hierarchy_transitive δ
  let := rankDomain_nonempty hδ.2.1
  let := hδ.rankCriterion.models_zf
  let P' : SetDomain (hierarchy δ) := ⟨P, hP⟩
  let π' : SetDomain (hierarchy δ) := ⟨π, hπ⟩
  let τ' : SetDomain (hierarchy δ) := ⟨τ, hτ⟩
  have hval := TransitiveZF.nameAction_val (hierarchy δ) P' π' τ'
    ((TransitiveZF.forcingName_iff (hierarchy δ) P' τ').mpr hn)
  exact hval ▸ (nameAction π' τ').property

end ZFVP
