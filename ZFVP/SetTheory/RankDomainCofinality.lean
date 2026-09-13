import ZFVP.SetTheory.NoncofinalMapBounds
import ZFVP.SetTheory.CofinalityDictionary
import ZFVP.SetTheory.RankBounds

/-! At a regular target above κ, bounds on each lower-rank domain combine
to a bound on the entire rank Vκ. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem hierarchy_map_bounded_of_small_bounds {κ μ f : V} [IsOrdinal κ]
    (hμ : IsRegularCardinal μ) (hκμ : κ ∈ μ)
    (hsucc : ∀ β ∈ κ, succ β ∈ κ)
    (hf : f ∈ μ ^ hierarchy κ)
    (hNo : ∀ β ∈ κ, ¬IsCofinalMap μ (hierarchy β) (f ↾ (hierarchy β))) :
    ∃ ξ ∈ μ, ∀ x ∈ hierarchy κ, f ‘ x ∈ ξ := by
  let := hμ.1.1
  let := IsFunction.of_mem hf
  let F : V → V := fun β ↦ ⋃ˢ range (f ↾ (hierarchy β))
  have hFdef : ℒₛₑₜ-function₁ F := by unfold F; definability
  have hres (β : V) (hβ : β ∈ κ) : f ↾ (hierarchy β) ∈ μ ^ hierarchy β := by
    let := IsOrdinal.of_mem hβ
    have hb : hierarchy β ⊆ hierarchy κ := hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hβ)
    apply restrict_mem_function_of_values
      (fun x hx ↦ (domain_eq_of_mem_function hf).symm ▸ hb x hx)
      (fun x hx ↦ function_value_mem hf (hb x hx))
  have hF (β : V) (hβ : β ∈ κ) : F β ∈ μ :=
    union_range_mem_of_not_cofinal (hres β hβ) (hNo β hβ)
  let g := definableGraph κ F hFdef
  have hg : g ∈ μ ^ κ := definableGraph_mem_function_of_mapsTo _ _ _ _ hF
  obtain ⟨ξ, hξ, hbound⟩ := regularCardinal_maps_bounded hμ hκμ hg
  refine ⟨ξ, hξ, ?_⟩
  intro x hx
  have hβ : succ (rank x) ∈ κ := hsucc _ ((mem_hierarchy_iff_rank_mem _ _).mp hx)
  have hxβ : x ∈ hierarchy (succ (rank x)) := (mem_hierarchy_iff_rank_mem _ _).mpr (by simp)
  have hfx : f ‘ x ∈ range (f ↾ (hierarchy (succ (rank x)))) := by
    have hh := value_mem_range (hres _ hβ) hxβ
    rwa [value_restrict ((domain_eq_of_mem_function hf).symm ▸ hx) hxβ] at hh
  have hsub : f ‘ x ⊆ F (succ (rank x)) := fun y hy ↦ mem_sUnion_iff.mpr ⟨f ‘ x, hfx, hy⟩
  have hFξ : F (succ (rank x)) ∈ ξ := by
    simpa only [g, value_definableGraph _ _ _ hβ] using hbound _ hβ
  let := IsOrdinal.of_mem (function_value_mem hf hx)
  let := IsOrdinal.of_mem (hF _ hβ)
  let := IsOrdinal.of_mem hξ
  rcases IsOrdinal.subset_iff.mp hsub with heq | hlt
  · exact heq ▸ hFξ
  · exact IsOrdinal.toIsTransitive.mem_trans hlt hFξ

theorem no_hierarchy_cofinalMap_of_small_bounds {κ μ : V} [IsOrdinal κ]
    (hμ : IsRegularCardinal μ) (hκμ : κ ∈ μ)
    (hsucc : ∀ β ∈ κ, succ β ∈ κ)
    (hNo : ∀ β ∈ κ, ∀ f, ¬IsCofinalMap μ (hierarchy β) f) :
    ∀ f, ¬IsCofinalMap μ (hierarchy κ) f := by
  intro f hf
  obtain ⟨ξ, hξ, hb⟩ := hierarchy_map_bounded_of_small_bounds hμ hκμ hsucc hf.1
    (fun β hβ ↦ hNo β hβ _)
  obtain ⟨x, hx, hξx⟩ := hf.2 ξ hξ
  exact mem_irrefl (f ‘ x) (hξx _ (hb x hx))

end ZFVP

