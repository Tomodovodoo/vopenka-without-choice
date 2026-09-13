import ZFVP.ModelTheory.CriticalPointCardinal
import ZFVP.ModelTheory.EmbeddingAssignments
import ZFVP.ModelTheory.EmbeddingOmegaFixation
import ZFVP.SetTheory.GroundUniquenessCoding
import ZFVP.SetTheory.InverseFunction
import ZFVP.SetTheory.RegularUnions
import ZFVP.SetTheory.CnAbsoluteness

/-! The pointwise image `imageSet f X = {f ‘ x | x ∈ X}` of a set under a coded membership
embedding, with the facts Kunen's inconsistency argument uses.

The domains are a pair of transitive sets `A`, `B`; only the closure statement
`imageSet f X ∈ hierarchy δ` needs `A = B = hierarchy δ` for a `Cn (k+1)` ordinal `δ`.

The pointwise image sits inside the value `f ‘ X` and agrees with it when `X` is the range of a
function on `ω` inside `A`. The restriction `f ↾ X` is an injection of `X` onto the pointwise
image. A critical point is never in the pointwise image of an ordinal it belongs to. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsCodedMembershipEmbedding

variable {A B f X : V} [IsTransitive A] [IsTransitive B]

omit [IsTransitive B] in
/-- A member of the domain set is a subset of the domain of the graph. -/
theorem subset_domain (h : IsCodedMembershipEmbedding A B f) (hX : X ∈ A) : X ⊆ domain f := by
  rw [domain_eq_of_mem_function h.function]
  exact fun x hx ↦ (inferInstance : IsTransitive A).mem_trans hx hX

omit [IsTransitive B] in
/-- Membership in the pointwise image. -/
theorem mem_imageSet_value_iff (h : IsCodedMembershipEmbedding A B f) (hX : X ∈ A) (y : V) :
    y ∈ imageSet f X ↔ ∃ x ∈ X, f ‘ x = y := by
  let := IsFunction.of_mem h.function
  exact mem_imageSet_iff (h.subset_domain hX) y

omit [IsTransitive B] in
/-- The pointwise image of `X` is a subset of the value of `X`. -/
theorem imageSet_subset_value (h : IsCodedMembershipEmbedding A B f) (hX : X ∈ A) :
    imageSet f X ⊆ f ‘ X := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (h.mem_imageSet_value_iff hX y).mp hy
  exact (h.value_mem_iff ((inferInstance : IsTransitive A).mem_trans hx hX) hX).mpr hx

omit [IsTransitive B] in
/-- A fixed set contains its own pointwise image. -/
theorem imageSet_subset_of_value_eq (h : IsCodedMembershipEmbedding A B f) (hX : X ∈ A)
    (hfix : f ‘ X = X) : imageSet f X ⊆ X := by
  intro y hy
  have := h.imageSet_subset_value hX y hy
  rwa [hfix] at this

omit [IsTransitive B] in
/-- The restriction of the graph to `X` is a function from `X` onto the pointwise image. -/
theorem restrict_mem_function (h : IsCodedMembershipEmbedding A B f) (hX : X ∈ A) :
    f ↾ X ∈ (imageSet f X) ^ X := by
  let := IsFunction.of_mem h.function
  exact function_mem_of_isFunction'
    (by rw [domain_restrict_eq, inter_eq_right_of_subset (h.subset_domain hX)]) rfl

omit [IsTransitive A] [IsTransitive B] in
/-- The restriction of the graph to `X` is injective. -/
theorem restrict_injective (h : IsCodedMembershipEmbedding A B f) : Injective (f ↾ X) :=
  fun x₁ x₂ y h₁ h₂ ↦
    h.injective x₁ x₂ y (restrict_subset f X _ h₁) (restrict_subset f X _ h₂)

omit [IsTransitive B] in
/-- Distinct members of `X` get distinct values. -/
theorem value_injOn (h : IsCodedMembershipEmbedding A B f) (hX : X ∈ A) :
    ∀ x ∈ X, ∀ y ∈ X, f ‘ x = f ‘ y → x = y := by
  intro x hx y hy he
  exact injective_value_eq h.function h.injective
    ((inferInstance : IsTransitive A).mem_trans hx hX)
    ((inferInstance : IsTransitive A).mem_trans hy hX) he

omit [IsTransitive B] in
/-- `X` injects into its pointwise image. -/
theorem cardLE_imageSet (h : IsCodedMembershipEmbedding A B f) (hX : X ∈ A) :
    X ≤# imageSet f X :=
  ⟨f ↾ X, h.restrict_mem_function hX, h.restrict_injective⟩

/-- If `X` is the range of a function on `ω` inside the domain, the value of `X` is its
pointwise image. -/
theorem value_eq_imageSet_of_omega_surjection (h : IsCodedMembershipEmbedding A B f)
    {g : V} (hω : (ω : V) ∈ A) (hX : X ∈ A) (hg : g ∈ A) (hgf : g ∈ X ^ (ω : V))
    (hr : range g = X) : f ‘ X = imageSet f X := by
  let := IsFunction.of_mem hgf
  have hmap := h.value_surjection hg hω hX hgf hr
  rw [h.value_omega hω] at hmap
  let := IsFunction.of_mem hmap.1
  apply subset_antisymm ?_ (h.imageSet_subset_value hX)
  intro y hy
  obtain ⟨n, hn⟩ := mem_range_iff.mp (hmap.2.symm ▸ hy)
  have hnω := (mem_of_mem_functions hmap.1 hn).1
  have hv := h.value_apply hg hω (IsFunction.of_mem hgf) (domain_eq_of_mem_function hgf) hnω
  rw [value_natural_of_omega_mem h hω hnω] at hv
  refine (h.mem_imageSet_value_iff hX _).mpr ⟨g ‘ n, function_value_mem hgf hnω, ?_⟩
  rw [← hv]
  exact value_eq_of_kpair_mem hn

end IsCodedMembershipEmbedding

/-- A critical point is not in the pointwise image of any ordinal of the domain. In particular it
is not in the pointwise image of an ordinal it belongs to. -/
theorem criticalPoint_not_mem_imageSet {A B f κ α : V} [IsTransitive A] [IsTransitive B]
    (h : IsCodedMembershipEmbedding A B f) (hκ : IsCriticalPoint A f κ)
    (hα : IsOrdinal α) (hαA : α ∈ A) : κ ∉ imageSet f α := by
  let := hκ.ordinal
  let := hα
  intro hmem
  obtain ⟨ξ, hξ, hfξ⟩ := (h.mem_imageSet_value_iff hαA κ).mp hmem
  have hξA : ξ ∈ A := (inferInstance : IsTransitive A).mem_trans hξ hαA
  have hξo : IsOrdinal ξ := IsOrdinal.of_mem hξ
  rcases IsOrdinal.mem_trichotomy ξ κ with hlt | heq | hgt
  · have hkξ : κ = ξ := hfξ.symm.trans (hκ.fixed_below hlt)
    rw [hkξ] at hlt
    exact mem_irrefl ξ hlt
  · exact hκ.moved (heq ▸ hfξ)
  · have hmv : f ‘ κ ∈ f ‘ ξ := (h.value_mem_iff hκ.mem_domain hξA).mpr hgt
    let := h.value_ordinal hξo hξA
    have hin : κ ∈ f ‘ ξ :=
      IsOrdinal.toIsTransitive.mem_trans (hκ.lt_value h) hmv
    rw [hfξ] at hin
    exact mem_irrefl κ hin

section Hierarchy

variable {k : ℕ} {δ f X : V}

/-- A rank stage of a `Cn (k+1)` ordinal contains the pointwise images of its members. -/
theorem imageSet_mem_hierarchy_of_embedding (hδ : Cn (k + 1) δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f) (hX : X ∈ hierarchy δ) :
    imageSet f X ∈ hierarchy δ := by
  let := hδ.ordinal
  let := hierarchy_transitive δ
  exact subset_mem_hierarchy_limit hδ.successor_closed (function_value_mem h.function hX)
    (h.imageSet_subset_value hX)

end Hierarchy

end ZFVP
