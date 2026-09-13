import ZFVP.SetTheory.SmallCollapseSurjection
import ZFVP.SetTheory.RegularCofinalSurjection
import ZFVP.ModelTheory.ElementaryBoundedWitness

/-! Function closure puts small subsets of an elementary submodel back in the submodel. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsElementaryInclusion
variable {Y B : V} (hY : IsElementaryInclusion Y B) [IsTransitive B]
include hY

theorem small_surjective_subset_mem {ν A F D e : V}
    (hclosure : (Y ∩ A) ^ (hierarchy ν) ⊆ Y)
    (hFsub : F ⊆ Y ∩ A) (hFB : F ∈ B)
    (he : e ∈ F ^ D) (hre : range e = F)
    (hDν : D ⊆ hierarchy ν) (hne : IsNonempty F) : F ∈ Y := by
  obtain ⟨g, hg, hgr⟩ := surjection_extension hDν he hre hne
  have hgY := hclosure g (mem_function_of_mem_function_of_subset hg hFsub)
  exact hgr ▸ hY.range_mem hgY (hgr.symm ▸ hFB)

theorem rank_surjective_subset_mem {ν δ A F e : V} [IsOrdinal ν] [IsOrdinal δ]
    (hclosure : (Y ∩ A) ^ (hierarchy ν) ⊆ Y)
    (hFsub : F ⊆ Y ∩ A) (hFB : F ∈ B)
    (he : e ∈ F ^ (hierarchy δ)) (hre : range e = F)
    (hδν : δ ∈ ν) (hne : IsNonempty F) : F ∈ Y :=
  hY.small_surjective_subset_mem hclosure hFsub hFB he hre
    (hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hδν)) hne

theorem small_collapse_subset_mem {ν A F X : V} [IsOrdinal ν]
    (hclosure : (Y ∩ A) ^ (hierarchy ν) ⊆ Y)
    (hFsub : F ⊆ Y ∩ A) (hFB : F ∈ B)
    (hX : HasSmallTransitiveCollapse ν X) (hFX : F ⊆ X)
    (hν : ∀ δ ∈ ν, succ δ ∈ ν) (hne : IsNonempty F) : F ∈ Y := by
  have hXne : IsNonempty X := by
    obtain ⟨a, ha⟩ := hne.nonempty
    exact ⟨a, hFX a ha⟩
  obtain ⟨δ, hδν, e, he, hre⟩ := hX.rank_surjection hXne hν
  have hrid : range (identity F) = F := by
    apply mem_ext
    intro z
    simp [mem_range_iff]
  obtain ⟨q, hq, hrq⟩ := surjection_extension hFX (identity_mem_function F) hrid hne
  let := IsOrdinal.of_mem hδν
  exact hY.rank_surjective_subset_mem hclosure hFsub hFB (compose_function he hq)
    (range_compose_surjective he hq hre hrq) hδν hne

end IsElementaryInclusion
end ZFVP
