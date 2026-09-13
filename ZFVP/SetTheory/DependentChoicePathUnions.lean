import ZFVP.SetTheory.DependentChoicePaths
import ZFVP.SetTheory.MonotoneCofinality
import ZFVP.SetTheory.FormulaReflection

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem compatible_range_of_increasing {B α H : V} [IsOrdinal α]
    (hH : H ∈ B ^ α) (hB : ∀ s ∈ B, IsFunction s)
    (hinc : ∀ i ∈ α, ∀ j ∈ i, H ‘ j ⊆ H ‘ i) :
    CompatibleFunctionFamily (range H) := by
  let := IsFunction.of_mem hH
  intro s hs t ht x y z hxy hxz
  obtain ⟨i, his⟩ := mem_range_iff.mp hs
  obtain ⟨j, hjt⟩ := mem_range_iff.mp ht
  have hi : i ∈ α := domain_eq_of_mem_function hH ▸ mem_domain_of_kpair_mem his
  have hj : j ∈ α := domain_eq_of_mem_function hH ▸ mem_domain_of_kpair_mem hjt
  have hs' : s = H ‘ i := (value_eq_of_kpair_mem his).symm
  have ht' : t = H ‘ j := (value_eq_of_kpair_mem hjt).symm
  subst s
  subst t
  let := hB (H ‘ i) (function_value_mem hH hi)
  let := hB (H ‘ j) (function_value_mem hH hj)
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  rcases IsOrdinal.mem_trichotomy i j with hij | rfl | hji
  · exact IsFunction.unique (hinc j hj i hij _ hxy) hxz
  · exact IsFunction.unique hxy hxz
  · exact IsFunction.unique hxy (hinc i hi j hji _ hxz)

theorem dependentChoicePath_union {A R B : V}
    (hB : ∀ s ∈ B, IsOrdinal (domain s) ∧ IsDependentChoicePath A R (domain s) s)
    (hC : CompatibleFunctionFamily B) :
    IsOrdinal (domain (⋃ˢ B)) ∧ IsDependentChoicePath A R (domain (⋃ˢ B)) (⋃ˢ B) := by
  have hF : ∀ s ∈ B, IsFunction s := fun s hs ↦ IsFunction.of_mem (hB s hs).2.1
  let := isFunction_sUnion hF hC
  have htrans : IsTransitive (domain (⋃ˢ B)) := ⟨by
    intro β hβ ξ hξ
    obtain ⟨s, hs, hβs⟩ := (mem_domain_sUnion_iff B β).mp hβ
    let := (hB s hs).1
    exact (mem_domain_sUnion_iff B ξ).mpr
      ⟨s, hs, IsOrdinal.toIsTransitive.mem_trans hξ hβs⟩⟩
  have hord : IsOrdinal (domain (⋃ˢ B)) := IsOrdinal.of_transitive_of_isOrdinal htrans (by
    intro β hβ
    obtain ⟨s, hs, hβs⟩ := (mem_domain_sUnion_iff B β).mp hβ
    let := (hB s hs).1
    exact IsOrdinal.of_mem hβs)
  refine ⟨hord, ⟨?_, ?_⟩⟩
  · apply mem_function_of_mem_function_of_subset (IsFunction.mem_function (⋃ˢ B))
    intro x hx
    obtain ⟨β, hβx⟩ := mem_range_iff.mp hx
    obtain ⟨s, hs, hp⟩ := mem_sUnion_iff.mp hβx
    exact range_subset_of_mem_function (hB s hs).2.1 _ (mem_range_of_kpair_mem hp)
  · intro β hβ
    obtain ⟨s, hs, hβs⟩ := (mem_domain_sUnion_iff B β).mp hβ
    let := hF s hs
    let := (hB s hs).1
    have hsub : β ⊆ domain s := IsOrdinal.toIsTransitive.transitive _ hβs
    have hsubU : β ⊆ domain (⋃ˢ B) := fun ξ hξ ↦
      (mem_domain_sUnion_iff B ξ).mpr ⟨s, hs, hsub ξ hξ⟩
    have hr : (⋃ˢ B) ↾ β = s ↾ β := restrict_eq_of_values hsubU hsub
      (fun ξ hξ ↦ value_sUnion_of_mem hF hC hs (hsub ξ hξ))
    rw [hr, value_sUnion_of_mem hF hC hs hβs]
    exact (hB s hs).2.2 β hβs

theorem dependentChoicePaths_union_bounded {κ A R i H : V} [IsOrdinal κ]
    (hi : i ∈ internalCofinality κ) (hH : H ∈ (dependentChoicePaths κ A R) ^ i)
    (hC : CompatibleFunctionFamily (range H)) :
    ⋃ˢ range H ∈ dependentChoicePaths κ A R := by
  let := IsFunction.of_mem hH
  have hpath (s : V) (hs : s ∈ range H) :
      domain s ∈ κ ∧ IsDependentChoicePath A R (domain s) s :=
    (mem_dependentChoicePaths _ _ _ _).mp (range_subset_of_mem_function hH s hs)
  obtain ⟨hord, hp⟩ := dependentChoicePath_union
    (fun s hs ↦ ⟨IsOrdinal.of_mem (hpath s hs).1, (hpath s hs).2⟩) hC
  let := hord
  let F := definableGraph i (fun j ↦ domain (H ‘ j)) (by definability)
  have hF : F ∈ κ ^ i := definableGraph_mem_function_of_mapsTo _ _ _ _ (by
    intro j hj
    exact ((mem_dependentChoicePaths _ _ _ _).mp (function_value_mem hH hj)).1)
  obtain ⟨ξ, hξ, hb⟩ := map_below_cofinality_bounded hi hF
  let := IsOrdinal.of_mem hξ
  have hsub : domain (⋃ˢ range H) ⊆ ξ := by
    intro β hβ
    obtain ⟨s, hs, hβs⟩ := (mem_domain_sUnion_iff _ _).mp hβ
    obtain ⟨j, hjs⟩ := mem_range_iff.mp hs
    have hj : j ∈ i := domain_eq_of_mem_function hH ▸ mem_domain_of_kpair_mem hjs
    have hd : domain s ∈ ξ := by
      have hh := hb j hj
      rw [show F ‘ j = domain (H ‘ j) from value_definableGraph _ _ _ hj,
        value_eq_of_kpair_mem hjs] at hh
      exact hh
    exact IsOrdinal.toIsTransitive.mem_trans hβs hd
  exact (mem_dependentChoicePaths _ _ _ _).mpr ⟨ordinal_mem_of_subset_mem hsub hξ, hp⟩

end ZFVP
