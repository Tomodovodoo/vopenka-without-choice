import ZFVP.SetTheory.InaccessibleWitnessClosure
import ZFVP.SetTheory.WoodinCollapseProjection
import ZFVP.SetTheory.OrdinalLeftOne

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem BoundsShortOrdinalMaps.small_subset_hierarchy {κ β X : V} [IsOrdinal β]
    (hb : BoundsShortOrdinalMaps κ β) (hz : (∅ : V) ∈ β) (hs : ∀ ξ ∈ β, succ ξ ∈ β)
    (hX : IsCardinalSmall κ X) (hsub : X ⊆ hierarchy β) : X ∈ hierarchy β := by
  classical
  by_cases hn : IsNonempty X
  · obtain ⟨γ, hγ, hi⟩ := hX
    obtain ⟨g, hg, hr⟩ := surjection_of_injection hi hn
    let := IsFunction.of_mem hg
    let F := definableGraph γ (fun i ↦ rank (g ‘ i)) (by definability)
    have hF : F ∈ β ^ γ := definableGraph_mem_function_of_mapsTo _ _ _ _
      (fun i hi ↦ (mem_hierarchy_iff_rank_mem _ β).mp (hsub _ (function_value_mem hg hi)))
    obtain ⟨ξ, hξ, hh⟩ := hb γ hγ F hF
    let := IsOrdinal.of_mem hξ
    apply mem_hierarchy_of_mem_stage (hs ξ hξ)
    rw [hierarchy_succ, mem_power_iff]
    intro x hx
    obtain ⟨i, hix⟩ := mem_range_iff.mp (hr.symm ▸ hx)
    have hiγ := domain_eq_of_mem_function hg ▸ mem_domain_of_kpair_mem hix
    have hv := hh i hiγ
    rw [show F ‘ i = rank (g ‘ i) from value_definableGraph _ _ _ hiγ, value_eq_of_kpair_mem hix] at hv
    exact (mem_hierarchy_iff_rank_mem _ ξ).mpr hv
  · have he : X = ∅ := by
      apply mem_ext
      intro x
      simp only [not_mem_empty, iff_false]
      exact fun hx ↦ hn ⟨x, hx⟩
    rw [he]
    exact ordinal_mem_hierarchy_iff.mpr hz

theorem ordinalAdd_one_mem_of_successor_closed {β η : V} [IsOrdinal β]
    (hs : ∀ ξ ∈ β, succ ξ ∈ β) (hη : η ∈ β) : ordinalAdd (1 : V) η ∈ β := by
  classical
  let := IsOrdinal.of_mem hη
  by_cases hn : η ∈ (ω : V)
  · rw [ordinalAdd_one_left_natural hn]
    exact hs η hη
  · rwa [ordinalAdd_one_left_infinite hn]

theorem woodinCollapseCut_mem_of_successor_closed {κ β δ p : V} [IsOrdinal β]
    (hs : ∀ ξ ∈ β, succ ξ ∈ β) (hp : p ∈ woodinCollapse κ δ) :
    woodinCollapseCut κ β p ∈ woodinCollapse κ β := by
  obtain ⟨ht, hf, _, hv⟩ := (mem_woodinCollapse _ _ _).mp hp
  let := hf
  have hc := woodinCollapse_subset hp (woodinCollapseCut_subset κ β p)
  obtain ⟨_, hcf, hcs, hcv⟩ := (mem_woodinCollapse _ _ _).mp hc
  refine (mem_woodinCollapse _ _ _).mpr ⟨?_, hcf, hcs, hcv⟩
  intro z hz
  obtain ⟨a, _, x, _, rfl⟩ := mem_prod_iff.mp (ht z (restrict_subset _ _ z hz))
  obtain ⟨α, hα, η, hη, rfl⟩ := mem_prod_iff.mp (kpair_mem_restrict_iff.mp hz).2
  let := IsOrdinal.of_mem hη
  have hb := ordinalAdd_one_mem_of_successor_closed hs hη
  let := IsOrdinal.of_mem hb
  exact kpair_mem_iff.mpr ⟨kpair_mem_iff.mpr ⟨hα, hη⟩,
    hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hb) x (hv α η x (restrict_subset _ _ _ hz))⟩

theorem woodinCollapse_condition_mem_of_short_bounds {κ β p : V} [IsOrdinal β]
    (hκ : IsRegularCardinal κ) (hκβ : κ ⊆ β) (hs : ∀ ξ ∈ β, succ ξ ∈ β)
    (hb : BoundsShortOrdinalMaps κ β) (hp : p ∈ woodinCollapse κ β) : p ∈ hierarchy β := by
  let := hκ.1.1
  obtain ⟨ht, hf, hsmall, _⟩ := (mem_woodinCollapse _ _ _).mp hp
  let := hf
  apply hb.small_subset_hierarchy (hκβ ∅ (hκ.2.1 ∅ (by simp))) hs
    (hsmall.of_cardLE (function_cardLE_domain p))
  intro z hz
  obtain ⟨a, ha, x, hx, rfl⟩ := mem_prod_iff.mp (ht z hz)
  obtain ⟨α, hα, η, hη, rfl⟩ := mem_prod_iff.mp ha
  let := IsOrdinal.of_mem hα
  let := IsOrdinal.of_mem hη
  exact kpair_mem_hierarchy_limit hs (kpair_mem_hierarchy_limit hs
    (ordinal_mem_hierarchy_iff.mpr (hκβ α hα)) (ordinal_mem_hierarchy_iff.mpr hη)) hx

theorem woodinCollapse_mem_of_low_rank {κ β δ p : V} [IsOrdinal β] [IsOrdinal δ]
    (hp : p ∈ woodinCollapse κ δ) (hlow : p ∈ hierarchy β) : p ∈ woodinCollapse κ β := by
  let := hierarchy_transitive β
  obtain ⟨ht, hf, hs, hv⟩ := (mem_woodinCollapse _ _ _).mp hp
  refine (mem_woodinCollapse _ _ _).mpr ⟨?_, hf, hs, hv⟩
  intro z hz
  obtain ⟨a, ha, x, _, rfl⟩ := mem_prod_iff.mp (ht z hz)
  obtain ⟨α, hα, η, hη, rfl⟩ := mem_prod_iff.mp ha
  have hl := kpair_components_mem_transitive ((hierarchy_transitive β).mem_trans hz hlow)
  have hηV := (kpair_components_mem_transitive hl.1).2
  let := IsOrdinal.of_mem hη
  exact kpair_mem_iff.mpr ⟨kpair_mem_iff.mpr ⟨hα, ordinal_mem_hierarchy_iff.mp hηV⟩, hl.2⟩

theorem woodinCollapse_union_of_cut_extension {κ β δ p q : V} [IsOrdinal β] [IsOrdinal δ]
    (hκ : IsRegularCardinal κ) (hβδ : β ⊆ δ) (hp : p ∈ woodinCollapse κ δ)
    (hq : q ∈ woodinCollapse κ β) (hext : woodinCollapseCut κ β p ⊆ q) :
    p ∪ q ∈ woodinCollapse κ δ := by
  let := ((mem_woodinCollapse _ _ _).mp hq).2.1
  apply woodinCollapse_union_two hκ hp (woodinCollapse_mono hβδ q hq)
  intro x y z hxy hxz
  have hx := (kpair_mem_iff.mp (((mem_woodinCollapse _ _ _).mp hq).1 _ hxz)).1
  exact IsFunction.unique (hext _ (kpair_mem_restrict_iff.mpr ⟨hxy, hx⟩)) hxz

end ZFVP
