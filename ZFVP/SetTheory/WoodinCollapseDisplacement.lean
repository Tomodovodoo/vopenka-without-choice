import ZFVP.SetTheory.WoodinCollapseRowAutomorphisms
import ZFVP.SetTheory.DisjointSupportSwap

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A collapse condition occupying every coordinate of either input, keeping the
first input's values where the two graphs disagree. -/
noncomputable def collapseSupportMerge (κ δ p q : V) : V :=
  p ∪ (q ↾ ((κ ×ˢ δ) \ domain p))

instance collapseSupportMerge_definable : ℒₛₑₜ-function₄[V] collapseSupportMerge := by
  unfold collapseSupportMerge
  definability

theorem collapseSupportMerge_condition {κ δ p q : V} (hκ : IsRegularCardinal κ)
    (hp : p ∈ woodinCollapse κ δ) (hq : q ∈ woodinCollapse κ δ) :
    collapseSupportMerge κ δ p q ∈ woodinCollapse κ δ := by
  apply woodinCollapse_binary_union hκ hp
    (woodinCollapse_subset hq (fun _ hz ↦ (mem_restrict_iff.mp hz).1))
  intro x y z hxy hxz
  have hx := (kpair_mem_restrict_iff.mp hxz).2
  have hn : x ∉ domain p := (mem_sdiff_iff.mp hx).2
  exact (hn (mem_domain_of_kpair_mem hxy)).elim

theorem collapseSupportMerge_domain_left (κ δ p q : V) :
    domain p ⊆ domain (collapseSupportMerge κ δ p q) := by
  intro x hx
  obtain ⟨y, hy⟩ := mem_domain_iff.mp hx
  exact mem_domain_of_kpair_mem (mem_union_iff.mpr (Or.inl hy))

theorem collapseSupportMerge_domain_right {κ δ p q : V}
    (hq : q ∈ woodinCollapse κ δ) :
    domain q ⊆ domain (collapseSupportMerge κ δ p q) := by
  intro x hx
  by_cases hp : x ∈ domain p
  · exact collapseSupportMerge_domain_left κ δ p q x hp
  · obtain ⟨y, hy⟩ := mem_domain_iff.mp hx
    exact mem_domain_of_kpair_mem (mem_union_iff.mpr (Or.inr
      (kpair_mem_restrict_iff.mpr ⟨hy, mem_sdiff_iff.mpr ⟨woodinCollapse_domain hq x hx, hp⟩⟩)))

noncomputable def collapseSupportInjection (κ δ p q : V) : V :=
  definableGraph (domain p)
    (fun x ↦ (converseGraph (collapseCoordinateMap κ δ (collapseSupportMerge κ δ p q))) ‘ x)
    (by definability)

instance collapseSupportInjection_definable : ℒₛₑₜ-function₄[V] collapseSupportInjection := by
  have h : ℒₛₑₜ-relation₅[V] (fun f κ δ p q ↦ ∀ z, z ∈ f ↔
    ∃ x ∈ domain p, z = ⟨x,
      (converseGraph (collapseCoordinateMap κ δ (collapseSupportMerge κ δ p q))) ‘ x⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [collapseSupportInjection, mem_definableGraph_iff]
  rfl

/-- The canonical row-preserving displacement, defined without choosing a
permutation separately at each coordinate. -/
noncomputable def woodinCollapseDisplacingCoordinates (κ δ p q : V) : V :=
  disjointSwap (κ ×ˢ δ) (domain p) (collapseSupportInjection κ δ p q)

instance woodinCollapseDisplacingCoordinates_definable :
    ℒₛₑₜ-function₄[V] woodinCollapseDisplacingCoordinates := by
  unfold woodinCollapseDisplacingCoordinates
  apply Language.DefinableFunction₃.comp
  · definability
  · definability
  · apply Language.DefinableFunction₄.comp <;> definability

theorem woodinCollapseDisplacingCoordinates_spec {κ δ p q : V}
    (hκ : IsRegularCardinal κ) (hp : p ∈ woodinCollapse κ δ)
    (hq : q ∈ woodinCollapse κ δ) :
    IsInternalPermutation (κ ×ˢ δ) (woodinCollapseDisplacingCoordinates κ δ p q) ∧
      (∀ z ∈ κ ×ˢ δ,
        kpair.π₂ ((woodinCollapseDisplacingCoordinates κ δ p q) ‘ z) = kpair.π₂ z) ∧
      ∀ x ∈ domain p, (woodinCollapseDisplacingCoordinates κ δ p q) ‘ x ∉ domain q := by
  let r := collapseSupportMerge κ δ p q
  have hr : r ∈ woodinCollapse κ δ := collapseSupportMerge_condition hκ hp hq
  let c := converseGraph (collapseCoordinateMap κ δ r)
  have hc : c ∈ (freeCollapseCoordinates κ δ r) ^ (κ ×ˢ δ) :=
    inverseCoordinateMap_function hκ hr
  have hfree : freeCollapseCoordinates κ δ r ⊆ κ ×ˢ δ :=
    fun x hx ↦ (mem_sdiff_iff.mp hx).1
  have hci : Injective c := by
    let := IsFunction.of_mem (collapseCoordinateMap_function hκ hr)
    exact converseGraph_injective _
  let f := definableGraph (domain p) (fun x ↦ c ‘ x) (by definability)
  have hf : f ∈ (κ ×ˢ δ) ^ (domain p) :=
    definableGraph_mem_function_of_mapsTo _ _ _ _
      (fun x hx ↦ hfree _ (function_value_mem hc (woodinCollapse_domain hp x hx)))
  have hfi : Injective f := by
    intro x y z hx hy
    obtain ⟨hxD, hzx⟩ := (pair_mem_definableGraph_iff _ _ (by definability) x z).mp hx
    obtain ⟨hyD, hzy⟩ := (pair_mem_definableGraph_iff _ _ (by definability) y z).mp hy
    exact injective_value_eq hc hci (woodinCollapse_domain hp x hxD)
      (woodinCollapse_domain hp y hyD) (hzx.symm.trans hzy)
  have hfval : ∀ x ∈ domain p, f ‘ x = c ‘ x :=
    fun _ hx ↦ value_definableGraph _ _ _ hx
  have hfr : ∀ x ∈ range f, x ∈ freeCollapseCoordinates κ δ r := by
    intro x hx
    obtain ⟨y, hy⟩ := mem_range_iff.mp hx
    let := IsFunction.of_mem hf
    have hyD := (mem_of_mem_functions hf hy).1
    rw [← value_eq_of_kpair_mem hy, hfval y hyD]
    exact function_value_mem hc (woodinCollapse_domain hp y hyD)
  have hdis : ∀ x ∈ range f, x ∉ domain p := by
    intro x hx hxD
    exact (mem_sdiff_iff.mp (hfr x hx)).2 (collapseSupportMerge_domain_left κ δ p q x hxD)
  have hrows : ∀ x ∈ domain p, kpair.π₂ (f ‘ x) = kpair.π₂ x := by
    intro x hx
    rw [hfval x hx]
    exact inverseCoordinateMap_preserves_row hκ hr (woodinCollapse_domain hp x hx)
  refine ⟨disjointSwap_permutation hf hfi (woodinCollapse_domain hp) hdis,
    disjointSwap_rows hf hfi hrows, ?_⟩
  intro x hx
  change ((disjointSwap (κ ×ˢ δ) (domain p) f) ‘ x ∉ domain q)
  rw [disjointSwap_value (woodinCollapse_domain hp x hx), disjointSwapValue_left hx, hfval x hx]
  intro hqD
  exact (mem_sdiff_iff.mp (function_value_mem hc (woodinCollapse_domain hp x hx))).2
    (collapseSupportMerge_domain_right hq _ hqD)

/-- Every pair of collapse conditions admits a ground coordinate permutation
moving the first support off the second support. No internal choice is required. -/
theorem woodinCollapse_displacing_permutation {κ δ p q : V}
    (hκ : IsRegularCardinal κ) (hp : p ∈ woodinCollapse κ δ)
    (hq : q ∈ woodinCollapse κ δ) :
    ∃ π, IsInternalPermutation (κ ×ˢ δ) π ∧
      (∀ z ∈ κ ×ˢ δ, kpair.π₂ (π ‘ z) = kpair.π₂ z) ∧
      ∀ x ∈ domain p, π ‘ x ∉ domain q :=
  ⟨woodinCollapseDisplacingCoordinates κ δ p q, woodinCollapseDisplacingCoordinates_spec hκ hp hq⟩

noncomputable def woodinCollapseDisplacement (κ δ p q : V) : V :=
  woodinCollapsePermutation κ δ (woodinCollapseDisplacingCoordinates κ δ p q)

instance woodinCollapseDisplacement_definable : ℒₛₑₜ-function₄[V] woodinCollapseDisplacement := by
  unfold woodinCollapseDisplacement
  apply Language.DefinableFunction₃.comp
  · definability
  · definability
  · apply Language.DefinableFunction₄.comp <;> definability

theorem woodinCollapseDisplacement_automorphism {κ δ p q : V}
    (hκ : IsRegularCardinal κ) (hp : p ∈ woodinCollapse κ δ)
    (hq : q ∈ woodinCollapse κ δ) :
    IsForcingAutomorphism (woodinCollapse κ δ) (woodinCollapseOrder κ δ)
      (woodinCollapseDisplacement κ δ p q) := by
  obtain ⟨hπ, hr, _⟩ := woodinCollapseDisplacingCoordinates_spec hκ hp hq
  exact woodinCollapsePermutation_automorphism hπ hr

theorem woodinCollapseDisplacement_common_extension {κ δ p q : V}
    (hκ : IsRegularCardinal κ) (hp : p ∈ woodinCollapse κ δ)
    (hq : q ∈ woodinCollapse κ δ) :
    ForcingCompatible (woodinCollapse κ δ) (woodinCollapseOrder κ δ)
      ((woodinCollapseDisplacement κ δ p q) ‘ p) q := by
  obtain ⟨hπ, hr, hd⟩ := woodinCollapseDisplacingCoordinates_spec hκ hp hq
  exact woodinCollapsePermutation_common_extension hκ hp hq hπ hr hd

theorem woodinCollapseDisplacement_empty {κ δ p q : V}
    (hp : p ∈ woodinCollapse κ δ) :
    (woodinCollapseDisplacement κ δ p q) ‘ ∅ = ∅ := by
  apply woodinCollapsePermutation_fixed (woodinCollapse_subset hp (empty_subset p))
  simp only [domain_empty]
  intro x hx
  exact (not_mem_empty hx).elim

/-- Weak homogeneity for the actual collapse forcing, witnessed by an automorphism
and an actual common extension. -/
theorem woodinCollapse_weak_homogeneous {κ δ p q : V}
    (hκ : IsRegularCardinal κ) (hp : p ∈ woodinCollapse κ δ)
    (hq : q ∈ woodinCollapse κ δ) :
    ∃ π, IsForcingAutomorphism (woodinCollapse κ δ) (woodinCollapseOrder κ δ) π ∧
      ∃ r ∈ woodinCollapse κ δ,
        ⟨r, π ‘ p⟩ₖ ∈ woodinCollapseOrder κ δ ∧ ⟨r, q⟩ₖ ∈ woodinCollapseOrder κ δ := by
  obtain ⟨π, hπ, hr, hd⟩ := woodinCollapse_displacing_permutation hκ hp hq
  exact ⟨woodinCollapsePermutation κ δ π, woodinCollapsePermutation_automorphism hπ hr,
    woodinCollapsePermutation_common_extension hκ hp hq hπ hr hd⟩

end ZFVP

