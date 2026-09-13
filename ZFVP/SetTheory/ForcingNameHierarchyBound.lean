import ZFVP.SetTheory.ForcingNameHierarchy
import ZFVP.SetTheory.ChoicelessInaccessibleRank
import ZFVP.SetTheory.RankCollection
import ZFVP.SetTheory.FiniteCodingClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingNameHierarchy_mem_hierarchy {P δ α : V} (hδ : IsChoicelessInaccessible δ)
    (hP : P ∈ hierarchy δ) (hα : α ∈ δ) : forcingNameHierarchy P α ∈ hierarchy δ := by
  let := hδ.1
  let := IsOrdinal.of_mem hα
  have hs : ∀ β ∈ δ, succ β ∈ δ := fun _ hb ↦ regularCardinal_succ_closed hδ.regular hb
  have hn : NoLowRankCofinalMaps δ := fun _ hX _ ↦ hδ.no_rank_cofinalMap hX
  have hall := transfinite_induction
    (fun α ↦ α ∈ δ → forcingNameHierarchy P α ∈ hierarchy δ) (by definability) ?_
  · exact hall (IsOrdinal.toOrdinal α) hα
  intro β ih hβ
  let F := fun γ ↦ ℘ (forcingNameHierarchy P γ ×ˢ P)
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let g := definableGraph (β : V) F hF
  have hg : g ∈ hierarchy δ ^ (β : V) := by
    apply definableGraph_mem_function_of_mapsTo
    intro γ hγ
    let := IsOrdinal.of_mem hγ
    exact power_mem_hierarchy_limit hs (prod_mem_hierarchy_limit hs
      (ih (IsOrdinal.toOrdinal γ) hγ (IsOrdinal.toIsTransitive.mem_trans hγ hβ)) hP)
  have hr : range g ∈ hierarchy δ := hn.range_mem hs (ordinal_mem_hierarchy_iff.mpr hβ) hg
  have he : forcingNameHierarchy P (β : V) = ⋃ˢ range g := by
    apply mem_ext
    intro ν
    rw [mem_forcingNameHierarchy, mem_sUnion_iff, show range g = repl F hF (β : V) from range_definableGraph _ _ _]
    simp only [repl_spec]
    constructor
    · rintro ⟨γ, hγ, hν⟩
      exact ⟨F γ, ⟨γ, hγ, rfl⟩, mem_power_iff.mpr hν⟩
    · rintro ⟨X, ⟨γ, hγ, rfl⟩, hν⟩
      exact ⟨γ, hγ, mem_power_iff.mp hν⟩
  rw [he]
  exact sUnion_mem_hierarchy_limit hs hr

end ZFVP
