import ZFVP.SetTheory.WoodinCollapseRows
import ZFVP.SetTheory.ReindexedPartialFunctions

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinCollapse_domain {κ δ p : V} (hp : p ∈ woodinCollapse κ δ) : domain p ⊆ κ ×ˢ δ := by
  intro x hx
  obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
  exact (kpair_mem_iff.mp (((mem_woodinCollapse _ _ _).mp hp).1 _ hxy)).1

theorem woodinCollapse_permuted {κ δ D π p : V} (hp : p ∈ woodinCollapse κ δ)
    (hπ : π ∈ (κ ×ˢ δ) ^ D) (hinj : Injective π) (hdom : domain p ⊆ D)
    (hrow : ∀ z ∈ D, kpair.π₂ (π ‘ z) = kpair.π₂ z) :
    permutedGraph π p ∈ woodinCollapse κ δ := by
  obtain ⟨hsub, hfun, hsmall, hval⟩ := (mem_woodinCollapse _ _ _).mp hp
  let := hfun
  refine (mem_woodinCollapse _ _ _).mpr ⟨?_, permutedGraph_function_of_injection hπ hinj hdom,
    hsmall.of_cardLE (permutedGraph_domain_cardLE hπ hinj hdom), ?_⟩
  · intro z hz
    obtain ⟨u, hu, rfl⟩ := (mem_permutedGraph π p z).mp hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hu
    have hy := (kpair_mem_iff.mp (hsub _ hu)).2
    simpa only [permutedGraphEntry, kpair.π₁_kpair, kpair.π₂_kpair] using
      kpair_mem_iff.mpr ⟨function_value_mem hπ (hdom x (mem_domain_of_kpair_mem hu)), hy⟩
  · intro α η x hx
    obtain ⟨u, hux, he⟩ := (pair_mem_permutedGraph π p _ x).mp hx
    obtain ⟨β, _, ξ, _, rfl⟩ := mem_prod_iff.mp (woodinCollapse_domain hp _ (mem_domain_of_kpair_mem hux))
    have hr := hrow _ (hdom _ (mem_domain_of_kpair_mem hux))
    rw [← he] at hr
    simp only [kpair.π₂_kpair] at hr
    exact hr.symm ▸ hval β ξ x hux

theorem inverseCoordinateMap_function {κ δ p : V} (hκ : IsRegularCardinal κ)
    (hp : p ∈ woodinCollapse κ δ) :
    converseGraph (collapseCoordinateMap κ δ p) ∈ (freeCollapseCoordinates κ δ p) ^ (κ ×ˢ δ) := by
  have h := converseGraph_mem_function (collapseCoordinateMap_function hκ hp)
    (collapseCoordinateMap_injective hκ hp)
  rwa [collapseCoordinateMap_range hκ hp] at h

theorem inverseCoordinateMap_preserves_row {κ δ p z : V} (hκ : IsRegularCardinal κ)
    (hp : p ∈ woodinCollapse κ δ) (hz : z ∈ κ ×ˢ δ) :
    kpair.π₂ ((converseGraph (collapseCoordinateMap κ δ p)) ‘ z) = kpair.π₂ z := by
  have hi := inverseCoordinateMap_function hκ hp
  have hr := collapseCoordinateMap_preserves_row (function_value_mem hi hz)
  rw [value_converseGraph_value (collapseCoordinateMap_function hκ hp)
    (collapseCoordinateMap_injective hκ hp) ((collapseCoordinateMap_range hκ hp).symm ▸ hz)] at hr
  exact hr.symm

theorem woodinCollapse_inverse_permuted {κ δ p q : V} (hκ : IsRegularCardinal κ)
    (hp : p ∈ woodinCollapse κ δ) (hq : q ∈ woodinCollapse κ δ) :
    permutedGraph (converseGraph (collapseCoordinateMap κ δ p)) q ∈ woodinCollapse κ δ := by
  have hi := inverseCoordinateMap_function hκ hp
  have hisub : freeCollapseCoordinates κ δ p ⊆ κ ×ˢ δ := by
    intro z hz
    exact (show z ∈ κ ×ˢ δ ∧ z ∉ domain p by simpa [freeCollapseCoordinates] using hz).1
  have hf := mem_function_of_mem_function_of_subset hi hisub
  let := IsFunction.of_mem (collapseCoordinateMap_function hκ hp)
  exact woodinCollapse_permuted hq hf (converseGraph_injective _) (woodinCollapse_domain hq)
    (fun z hz ↦ inverseCoordinateMap_preserves_row hκ hp hz)

theorem woodinCollapse_inverse_permuted_domain {κ δ p q : V} (hκ : IsRegularCardinal κ)
    (hp : p ∈ woodinCollapse κ δ) (hq : q ∈ woodinCollapse κ δ) :
    domain (permutedGraph (converseGraph (collapseCoordinateMap κ δ p)) q) ⊆
      freeCollapseCoordinates κ δ p := by
  let := ((mem_woodinCollapse _ _ _).mp hq).2.1
  intro z hz
  obtain ⟨u, hu, rfl⟩ := permutedGraph_domain_maps hz
  exact function_value_mem (inverseCoordinateMap_function hκ hp) (woodinCollapse_domain hq _ hu)

theorem woodinCollapse_binary_union {κ δ p q : V} (hκ : IsRegularCardinal κ)
    (hp : p ∈ woodinCollapse κ δ) (hq : q ∈ woodinCollapse κ δ)
    (hc : ∀ x y z, ⟨x, y⟩ₖ ∈ p → ⟨x, z⟩ₖ ∈ q → y = z) :
    p ∪ q ∈ woodinCollapse κ δ := by
  have hF : ∀ f ∈ ({p, q} : V), f ∈ woodinCollapse κ δ := by
    intro f hf
    rcases show f = p ∨ f = q from by simpa using hf with rfl | rfl <;> assumption
  have hC : CompatibleFunctionFamily ({p, q} : V) := by
    let := ((mem_woodinCollapse _ _ _).mp hp).2.1
    let := ((mem_woodinCollapse _ _ _).mp hq).2.1
    intro f hf g hg x y z hxy hxz
    have hff : f = p ∨ f = q := by simpa using hf
    have hgg : g = p ∨ g = q := by simpa using hg
    rcases hff with rfl | rfl <;> rcases hgg with rfl | rfl
    · exact IsFunction.unique hxy hxz
    · exact hc x y z hxy hxz
    · exact (hc x z y hxz hxy).symm
    · exact IsFunction.unique hxy hxz
  have he : domain (p ∪ q) = domain p ∪ domain q := by
    ext x
    simp only [mem_domain_iff, mem_union_iff, exists_or]
  have hs : IsCardinalSmall κ (domain (p ∪ q)) := by
    rw [he]
    exact ((mem_woodinCollapse _ _ _).mp hp).2.2.1.union hκ
      ((mem_woodinCollapse _ _ _).mp hq).2.2.1
  have hs' : IsCardinalSmall κ (domain (⋃ˢ ({p, q} : V))) := by simpa using hs
  simpa using woodinCollapse_union hF hC hs'

end ZFVP
