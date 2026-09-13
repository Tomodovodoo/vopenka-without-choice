import ZFVP.SetTheory.CardinalSmallUnions
import ZFVP.SetTheory.CnAbsoluteness

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem function_cardLE_domain (f : V) [IsFunction f] : f ≤# domain f := by
  let g := definableGraph f kpair.π₁ (by definability)
  have hg : g ∈ (domain f) ^ f := definableGraph_mem_function_of_mapsTo _ _ _ _ (by
    intro z hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    simpa using mem_domain_of_kpair_mem hz)
  refine ⟨g, hg, ?_⟩
  intro x y z hx hy
  obtain ⟨hxF, hzx⟩ := (pair_mem_definableGraph_iff _ _ (by definability) x z).mp hx
  obtain ⟨hyF, hzy⟩ := (pair_mem_definableGraph_iff _ _ (by definability) y z).mp hy
  obtain ⟨a, b, rfl⟩ := IsFunction.mem_eq_kpair hxF
  obtain ⟨c, d, rfl⟩ := IsFunction.mem_eq_kpair hyF
  have hac : a = c := by simpa using hzx.symm.trans hzy
  subst c
  exact kpair_iff.mpr ⟨rfl, IsFunction.unique hxF hyF⟩

theorem regularCardinal_small_subset_hierarchy {κ A : V} (hκ : IsRegularCardinal κ)
    (hA : IsCardinalSmall κ A) (hsub : A ⊆ hierarchy κ) : A ∈ hierarchy κ := by
  classical
  let := hκ.1.1
  by_cases hn : IsNonempty A
  · obtain ⟨α, hα, hinj⟩ := hA
    obtain ⟨g, hg, hr⟩ := surjection_of_injection hinj hn
    let := IsFunction.of_mem hg
    let F := definableGraph α (fun i ↦ rank (g ‘ i)) (by definability)
    have hF : F ∈ κ ^ α := definableGraph_mem_function_of_mapsTo _ _ _ _ (by
      intro i hi
      exact (mem_hierarchy_iff_rank_mem _ κ).mp (hsub _ (function_value_mem hg hi)))
    obtain ⟨β, hβ, hb⟩ := regularCardinal_maps_bounded hκ hα hF
    let := IsOrdinal.of_mem hβ
    apply mem_hierarchy_of_mem_stage (regularCardinal_succ_closed hκ hβ)
    rw [hierarchy_succ, mem_power_iff]
    intro x hx
    have hxr : x ∈ range g := hr.symm ▸ hx
    obtain ⟨i, hi⟩ := mem_range_iff.mp hxr
    have hiα : i ∈ α := domain_eq_of_mem_function hg ▸ mem_domain_of_kpair_mem hi
    have hgi := value_eq_of_kpair_mem hi
    have hri := hb i hiα
    rw [show F ‘ i = rank (g ‘ i) from value_definableGraph _ _ _ hiα, hgi] at hri
    exact (mem_hierarchy_iff_rank_mem _ β).mpr hri
  · have he : A = ∅ := by
      apply mem_ext
      intro z
      simp only [not_mem_empty, iff_false]
      exact fun hz ↦ hn ⟨z, hz⟩
    rw [he]
    exact ordinal_mem_hierarchy_iff.mpr (hκ.2.1 ∅ (by simp))

end ZFVP
