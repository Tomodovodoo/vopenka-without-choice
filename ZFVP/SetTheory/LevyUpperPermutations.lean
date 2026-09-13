import ZFVP.SetTheory.LevyCollapseRowPermutations
import ZFVP.SetTheory.LevyCollapseUpper
import ZFVP.SetTheory.HomogeneousForcing
import ZFVP.ModelTheory.SubposetRealization

/-! Row permutations above `β` act on the upper collapse `Coll(ω,[β,κ))` and make it weakly
homogeneous. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem levyCut_union_distrib (β p q : V) : levyCut β (p ∪ q) = levyCut β p ∪ levyCut β q := by
  ext z
  simp only [levyCut, mem_restrict_iff, mem_union_iff]
  constructor
  · rintro ⟨h | h, hz⟩
    · exact Or.inl ⟨h, hz⟩
    · exact Or.inr ⟨h, hz⟩
  · rintro (⟨h, hz⟩ | ⟨h, hz⟩)
    · exact ⟨Or.inl h, hz⟩
    · exact ⟨Or.inr h, hz⟩

section

variable {κ β σ : V}

/-- A coordinate lies below `β` exactly when its image under a column-preserving permutation
does. -/
theorem coordinate_mem_iff_of_preservesColumns {π x : V}
    (hπ : IsInternalPermutation ((ω : V) ×ˢ κ) π) (hcol : PreservesColumns κ π)
    (hx : x ∈ (ω : V) ×ˢ κ) : π ‘ x ∈ (ω : V) ×ˢ β ↔ x ∈ (ω : V) ×ˢ β := by
  obtain ⟨n, hn, α, hα, rfl⟩ := mem_prod_iff.mp hx
  have hc := hcol _ hx
  have hπx : π ‘ ⟨n, α⟩ₖ ∈ (ω : V) ×ˢ κ := function_value_mem hπ.1 hx
  obtain ⟨n', hn', α', _, he⟩ := mem_prod_iff.mp hπx
  rw [he] at hc ⊢
  simp only [kpair.π₂_kpair] at hc
  rw [hc, kpair_mem_iff, kpair_mem_iff]
  exact ⟨fun h ↦ ⟨hn, h.2⟩, fun h ↦ ⟨hn', h.2⟩⟩

/-- Row permutations map conditions above `β` to conditions above `β`. -/
theorem permutedGraph_mem_above (hσ : IsInternalPermutation (ω : V) σ) {p : V}
    (hp : p ∈ levyCollapseAbove κ β) :
    permutedGraph (levyRowPermutation κ β σ) p ∈ levyCollapseAbove κ β := by
  have hπ := levyRowPermutation_permutation (κ := κ) (β := β) hσ
  have hcol := levyRowPermutation_preservesColumns (κ := κ) (β := β) hσ
  have hpC := levyCollapseAbove_subset κ β p hp
  refine (mem_levyCollapseAbove_iff _ _ _).mpr ⟨permutedGraph_levy_mem hπ hcol hpC, ?_⟩
  ext z
  simp only [not_mem_empty, iff_false]
  intro hz
  obtain ⟨hzp, x, hx, y, rfl⟩ := mem_restrict_iff.mp hz
  haveI : IsFunction p :=
    ((mem_finitePartialFunctions _ _ p).mp (levyCollapse_finitePartialFunction hpC)).2.1
  obtain ⟨u, hu, rfl⟩ := (pair_mem_permutedGraph _ p _ y).mp hzp
  have hsub := ((mem_finitePartialFunctions _ _ p).mp (levyCollapse_finitePartialFunction hpC)).1
  have huκ := (kpair_mem_iff.mp (hsub _ hu)).1
  exact coordinate_not_mem_of_above hp hu
    ((coordinate_mem_iff_of_preservesColumns hπ hcol huκ).mp hx)

/-- The automorphism of the upper collapse induced by a row permutation. -/
noncomputable def levyUpperPermutation (κ β σ : V) : V :=
  definableGraph (levyCollapseAbove κ β) (fun p ↦ (levyPermutation κ β σ) ‘ p) (by definability)

theorem levyUpperPermutation_value {p : V} (hp : p ∈ levyCollapseAbove κ β) :
    (levyUpperPermutation κ β σ) ‘ p = (levyPermutation κ β σ) ‘ p :=
  value_definableGraph _ _ _ hp

theorem levyUpperPermutation_value_graph {p : V} (hp : p ∈ levyCollapseAbove κ β) :
    (levyUpperPermutation κ β σ) ‘ p = permutedGraph (levyRowPermutation κ β σ) p := by
  rw [levyUpperPermutation_value hp, levyPermutation_value (levyCollapseAbove_subset κ β p hp)]

theorem levyPermutation_value_mem_above (hσ : IsInternalPermutation (ω : V) σ) {p : V}
    (hp : p ∈ levyCollapseAbove κ β) : (levyPermutation κ β σ) ‘ p ∈ levyCollapseAbove κ β := by
  rw [levyPermutation_value (levyCollapseAbove_subset κ β p hp)]
  exact permutedGraph_mem_above hσ hp

theorem levyUpperPermutation_function (hσ : IsInternalPermutation (ω : V) σ) :
    levyUpperPermutation κ β σ ∈ levyCollapseAbove κ β ^ levyCollapseAbove κ β :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun p hp ↦ levyPermutation_value_mem_above hσ hp)

theorem levyUpperPermutation_automorphism (hσ : IsInternalPermutation (ω : V) σ) :
    IsForcingAutomorphism (levyCollapseAbove κ β)
      (restrictedOrder (levyOrder κ) (levyCollapseAbove κ β)) (levyUpperPermutation κ β σ) := by
  have hf := levyUpperPermutation_function (κ := κ) (β := β) hσ
  have hπ := levyPermutation_automorphism (κ := κ) (β := β) hσ
  haveI : IsFunction (levyUpperPermutation κ β σ) := IsFunction.of_mem hf
  haveI : IsFunction (levyPermutation κ β σ) := IsFunction.of_mem hπ.1
  have hπdom : domain (levyPermutation κ β σ) = levyCollapse κ := domain_eq_of_mem_function hπ.1
  refine ⟨hf, ?_, ?_, ?_⟩
  · intro p q z hp hq
    have hpA := (mem_of_mem_functions hf hp).1
    have hqA := (mem_of_mem_functions hf hq).1
    have h1 := value_eq_of_kpair_mem hp
    have h2 := value_eq_of_kpair_mem hq
    rw [levyUpperPermutation_value hpA] at h1
    rw [levyUpperPermutation_value hqA] at h2
    apply hπ.2.1 p q z
    · rw [← h1]
      exact kpair_value_mem (by rw [hπdom]; exact levyCollapseAbove_subset κ β p hpA)
    · rw [← h2]
      exact kpair_value_mem (by rw [hπdom]; exact levyCollapseAbove_subset κ β q hqA)
  · apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
    intro q hq
    obtain ⟨p, hp, hpq⟩ := forcingAutomorphism_surjective hπ q (levyCollapseAbove_subset κ β q hq)
    have hpA : p ∈ levyCollapseAbove κ β := by
      refine (mem_levyCollapseAbove_iff _ _ _).mpr ⟨hp, ?_⟩
      ext z
      simp only [not_mem_empty, iff_false]
      intro hz
      obtain ⟨hzp, x, hx, y, rfl⟩ := mem_restrict_iff.mp hz
      have hsub := ((mem_finitePartialFunctions _ _ p).mp (levyCollapse_finitePartialFunction hp)).1
      have hxκ := (kpair_mem_iff.mp (hsub _ hzp)).1
      have hmem : ⟨(levyRowPermutation κ β σ) ‘ x, y⟩ₖ ∈ permutedGraph (levyRowPermutation κ β σ) p :=
        (mem_permutedGraph _ _ _).mpr ⟨⟨x, y⟩ₖ, hzp, by
          simp only [permutedGraphEntry, kpair.π₁_kpair, kpair.π₂_kpair]⟩
      rw [← levyPermutation_value hp, hpq] at hmem
      exact coordinate_not_mem_of_above hq hmem
        ((coordinate_mem_iff_of_preservesColumns (levyRowPermutation_permutation hσ)
          (levyRowPermutation_preservesColumns hσ) hxκ).mpr hx)
    have hv : (levyUpperPermutation κ β σ) ‘ p = q := by
      rw [levyUpperPermutation_value hpA, hpq]
    exact hv ▸ value_mem_range hf hpA
  · intro p hp q hq
    rw [kpair_mem_restrictedOrder_iff, kpair_mem_restrictedOrder_iff,
      levyUpperPermutation_value hp, levyUpperPermutation_value hq]
    have hp' := levyPermutation_value_mem_above hσ hp
    have hq' := levyPermutation_value_mem_above hσ hq
    have hord := hπ.2.2.2 p (levyCollapseAbove_subset κ β p hp) q (levyCollapseAbove_subset κ β q hq)
    simp only [hp, hq, hp', hq', and_true]
    exact hord

theorem levyUpperPermutation_top (hσ : IsInternalPermutation (ω : V) σ) (hβ : β ⊆ κ) :
    (levyUpperPermutation κ β σ) ‘ (∅ : V) = ∅ := by
  rw [levyUpperPermutation_value (empty_mem_levyCollapseAbove κ β)]
  exact levyPermutation_fixed hσ (empty_mem_levyCollapse β) hβ

/-- The upper collapse is weakly homogeneous. -/
theorem levyCollapseAbove_homogeneous (hβ : β ⊆ κ) :
    IsWeaklyHomogeneous (levyCollapseAbove κ β)
      (restrictedOrder (levyOrder κ) (levyCollapseAbove κ β)) ∅ := by
  intro p hp q hq
  have hpC := levyCollapseAbove_subset κ β p hp
  have hqC := levyCollapseAbove_subset κ β q hq
  obtain ⟨σ, hσ, hmove⟩ := exists_permutation_moving (levyRows_finite (β := β) hpC)
    (levyRows_subset β p) (levyRows_finite (β := β) hqC) (levyRows_subset β q)
  refine ⟨levyUpperPermutation κ β σ, levyUpperPermutation_automorphism hσ,
    levyUpperPermutation_top hσ hβ, ?_⟩
  have hcut : levyCut β p ⊆ q := by
    rw [((mem_levyCollapseAbove_iff _ _ _).mp hp).2]
    exact fun z hz ↦ absurd hz not_mem_empty
  have hcompat := levyPermutation_compatible hσ hpC hqC hcut hmove
  have hπp : permutedGraph (levyRowPermutation κ β σ) p ∈ levyCollapseAbove κ β :=
    permutedGraph_mem_above hσ hp
  have hr : permutedGraph (levyRowPermutation κ β σ) p ∪ q ∈ levyCollapse κ :=
    levyCollapse_union (levyCollapseAbove_subset κ β _ hπp) hqC hcompat
  have hrA : permutedGraph (levyRowPermutation κ β σ) p ∪ q ∈ levyCollapseAbove κ β := by
    refine (mem_levyCollapseAbove_iff _ _ _).mpr ⟨hr, ?_⟩
    rw [levyCut_union_distrib, ((mem_levyCollapseAbove_iff _ _ _).mp hπp).2,
      ((mem_levyCollapseAbove_iff _ _ _).mp hq).2]
    ext z
    simp
  rw [levyUpperPermutation_value_graph hp]
  refine ⟨_, hrA, ?_, ?_⟩
  · exact (kpair_mem_restrictedOrder_iff _ _ _ _).mpr
      ⟨(pair_mem_reverseInclusionOrder _ _ _).mpr
        ⟨hr, levyCollapseAbove_subset κ β _ hπp, subset_union_left _ _⟩, hrA, hπp⟩
  · exact (kpair_mem_restrictedOrder_iff _ _ _ _).mpr
      ⟨(pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hr, hqC, subset_union_right _ _⟩, hrA, hq⟩

end

end ZFVP
