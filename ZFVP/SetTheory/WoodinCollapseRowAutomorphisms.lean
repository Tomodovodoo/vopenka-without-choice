import ZFVP.SetTheory.WoodinCollapseHomogeneity
import ZFVP.SetTheory.InternalTranspositions

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Reindexing collapse coordinates by a row-preserving permutation. -/
noncomputable def woodinCollapsePermutation (κ δ π : V) : V :=
  definableGraph (woodinCollapse κ δ) (permutedGraph π) (by definability)

instance woodinCollapsePermutation_definable :
    ℒₛₑₜ-function₃[V] woodinCollapsePermutation := by
  have h : ℒₛₑₜ-relation₄[V] (fun f κ δ π ↦ ∀ z, z ∈ f ↔
      ∃ p ∈ woodinCollapse κ δ, z = ⟨p, permutedGraph π p⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinCollapsePermutation (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [woodinCollapsePermutation, mem_definableGraph_iff]

theorem woodinCollapsePermutation_value {κ δ π p : V}
    (hp : p ∈ woodinCollapse κ δ) :
    (woodinCollapsePermutation κ δ π) ‘ p = permutedGraph π p :=
  value_definableGraph _ _ _ hp

theorem rowPermutation_inverse {κ δ π : V}
    (hπ : IsInternalPermutation (κ ×ˢ δ) π)
    (hr : ∀ z ∈ κ ×ˢ δ, kpair.π₂ (π ‘ z) = kpair.π₂ z) :
    ∀ z ∈ κ ×ˢ δ, kpair.π₂ ((converseGraph π) ‘ z) = kpair.π₂ z := by
  intro z hz
  have h := hr _ (function_value_mem hπ.inv.1 hz)
  rw [hπ.value_inv hz] at h
  exact h.symm

theorem woodinCollapsePermutation_automorphism {κ δ π : V}
    (hπ : IsInternalPermutation (κ ×ˢ δ) π)
    (hr : ∀ z ∈ κ ×ˢ δ, kpair.π₂ (π ‘ z) = kpair.π₂ z) :
    IsForcingAutomorphism (woodinCollapse κ δ) (woodinCollapseOrder κ δ)
      (woodinCollapsePermutation κ δ π) := by
  have hF : ∀ p ∈ woodinCollapse κ δ, permutedGraph π p ∈ woodinCollapse κ δ :=
    fun _ hp ↦ woodinCollapse_permuted hp hπ.1 hπ.2.1 (woodinCollapse_domain hp) hr
  have hG : ∀ p ∈ woodinCollapse κ δ,
      permutedGraph (converseGraph π) p ∈ woodinCollapse κ δ :=
    fun _ hp ↦ woodinCollapse_permuted hp hπ.inv.1 hπ.inv.2.1
      (woodinCollapse_domain hp) (rowPermutation_inverse hπ hr)
  have hGF : ∀ p ∈ woodinCollapse κ δ,
      permutedGraph (converseGraph π) (permutedGraph π p) = p := by
    intro p hp
    let := ((mem_woodinCollapse _ _ _).mp hp).2.1
    exact permutedGraph_inverse_of_values (fun x hx ↦ hπ.inv_value (woodinCollapse_domain hp x hx))
  have hFG : ∀ p ∈ woodinCollapse κ δ,
      permutedGraph π (permutedGraph (converseGraph π) p) = p := by
    intro p hp
    let := ((mem_woodinCollapse _ _ _).mp hp).2.1
    exact permutedGraph_inverse_of_values (fun x hx ↦ hπ.value_inv (woodinCollapse_domain hp x hx))
  exact reverseInclusion_isomorphism_of_inverse _ _ (by definability) hF hG hGF hFG
    (fun _ _ _ _ h ↦ permutedGraph_mono h) (fun _ _ _ _ h ↦ permutedGraph_mono h)

theorem woodinCollapsePermutation_fixed {κ δ π p : V}
    (hp : p ∈ woodinCollapse κ δ) (hfix : ∀ x ∈ domain p, π ‘ x = x) :
    (woodinCollapsePermutation κ δ π) ‘ p = p := by
  rw [woodinCollapsePermutation_value hp]
  let := ((mem_woodinCollapse _ _ _).mp hp).2.1
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨u, hu, rfl⟩ := (mem_permutedGraph _ _ _).mp hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hu
    simpa only [permutedGraphEntry, kpair.π₁_kpair, kpair.π₂_kpair,
      hfix x (mem_domain_of_kpair_mem hu)] using hu
  · intro hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    exact (pair_mem_permutedGraph _ _ _ _).mpr
      ⟨x, hz, (hfix x (mem_domain_of_kpair_mem hz)).symm⟩

/-- Disjointness of the moved domain gives the required common extension. -/
theorem woodinCollapsePermutation_common_extension {κ δ π p q : V}
    (hκ : IsRegularCardinal κ) (hp : p ∈ woodinCollapse κ δ)
    (hq : q ∈ woodinCollapse κ δ) (hπ : IsInternalPermutation (κ ×ˢ δ) π)
    (hr : ∀ z ∈ κ ×ˢ δ, kpair.π₂ (π ‘ z) = kpair.π₂ z)
    (hd : ∀ x ∈ domain p, π ‘ x ∉ domain q) :
    ∃ r ∈ woodinCollapse κ δ,
      ⟨r, (woodinCollapsePermutation κ δ π) ‘ p⟩ₖ ∈ woodinCollapseOrder κ δ ∧
      ⟨r, q⟩ₖ ∈ woodinCollapseOrder κ δ := by
  have hp' := woodinCollapse_permuted hp hπ.1 hπ.2.1 (woodinCollapse_domain hp) hr
  let := ((mem_woodinCollapse _ _ _).mp hp).2.1
  have hc : ∀ x y z, ⟨x, y⟩ₖ ∈ permutedGraph π p → ⟨x, z⟩ₖ ∈ q → y = z := by
    intro x y z hxy hxz
    obtain ⟨u, hu, rfl⟩ := (pair_mem_permutedGraph _ _ _ _).mp hxy
    exact (hd u (mem_domain_of_kpair_mem hu) (mem_domain_of_kpair_mem hxz)).elim
  have hu := woodinCollapse_binary_union hκ hp' hq hc
  refine ⟨permutedGraph π p ∪ q, hu, ?_, ?_⟩
  · rw [woodinCollapsePermutation_value hp, woodinCollapseOrder, pair_mem_reverseInclusionOrder]
    exact ⟨hu, hp', fun z hz ↦ mem_union_iff.mpr (Or.inl hz)⟩
  · rw [woodinCollapseOrder, pair_mem_reverseInclusionOrder]
    exact ⟨hu, hq, fun z hz ↦ mem_union_iff.mpr (Or.inr hz)⟩

theorem woodinCollapsePermutation_inverse_value {κ δ π p : V}
    (hπ : IsInternalPermutation (κ ×ˢ δ) π)
    (hr : ∀ z ∈ κ ×ˢ δ, kpair.π₂ (π ‘ z) = kpair.π₂ z)
    (hp : p ∈ woodinCollapse κ δ) :
    (woodinCollapsePermutation κ δ (converseGraph π)) ‘
      ((woodinCollapsePermutation κ δ π) ‘ p) = p := by
  have hm := woodinCollapse_permuted hp hπ.1 hπ.2.1 (woodinCollapse_domain hp) hr
  rw [woodinCollapsePermutation_value hp, woodinCollapsePermutation_value hm]
  let := ((mem_woodinCollapse _ _ _).mp hp).2.1
  exact permutedGraph_inverse_of_values
    (fun x hx ↦ hπ.inv_value (woodinCollapse_domain hp x hx))

/-- A swap inside one collapse row preserves the row of every coordinate. -/
theorem woodinCollapse_transposition_rows {κ δ a b η : V} :
    ∀ z ∈ κ ×ˢ δ,
      kpair.π₂ ((internalTransposition (κ ×ˢ δ) ⟨a, η⟩ₖ ⟨b, η⟩ₖ) ‘ z) =
        kpair.π₂ z := by
  intro z hz
  rw [internalTransposition_value hz]
  by_cases ha : z = ⟨a, η⟩ₖ
  · subst z
    rw [transpositionValue_left, kpair.π₂_kpair, kpair.π₂_kpair]
  · by_cases hb : z = ⟨b, η⟩ₖ
    · subst z
      rw [transpositionValue_right, kpair.π₂_kpair, kpair.π₂_kpair]
    · rw [transpositionValue_fixed ha hb]

theorem woodinCollapse_transposition_automorphism {κ δ a b η : V}
    (ha : a ∈ κ) (hb : b ∈ κ) (hη : η ∈ δ) :
    IsForcingAutomorphism (woodinCollapse κ δ) (woodinCollapseOrder κ δ)
      (woodinCollapsePermutation κ δ
        (internalTransposition (κ ×ˢ δ) ⟨a, η⟩ₖ ⟨b, η⟩ₖ)) :=
  woodinCollapsePermutation_automorphism
    (internalTransposition_permutation (kpair_mem_iff.mpr ⟨ha, hη⟩)
      (kpair_mem_iff.mpr ⟨hb, hη⟩)) woodinCollapse_transposition_rows

/-- The explicit swap acts trivially on every condition avoiding its two coordinates. -/
theorem woodinCollapse_transposition_fixed {κ δ a b η p : V}
    (hp : p ∈ woodinCollapse κ δ)
    (ha : ⟨a, η⟩ₖ ∉ domain p) (hb : ⟨b, η⟩ₖ ∉ domain p) :
    (woodinCollapsePermutation κ δ
      (internalTransposition (κ ×ˢ δ) ⟨a, η⟩ₖ ⟨b, η⟩ₖ)) ‘ p = p := by
  apply woodinCollapsePermutation_fixed hp
  intro x hx
  exact internalTransposition_fixed (woodinCollapse_domain hp x hx)
    (fun he ↦ ha (he ▸ hx)) (fun he ↦ hb (he ▸ hx))

end ZFVP


