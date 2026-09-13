import ZFVP.SetTheory.InternalOrderType

/-! The order types of well-orders on subsets of any internal set form a set. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def wellOrderCodes (A : V) : V :=
  {p ∈ ℘ A ×ˢ ℘ (A ×ˢ A) ; IsInternalWellOrder (kpair.π₂ p) (kpair.π₁ p)}

instance wellOrderCodes_definable : ℒₛₑₜ-function₁[V] wellOrderCodes := by
  have h : ℒₛₑₜ-relation (fun C A : V ↦ ∀ p, p ∈ C ↔ p ∈ ℘ A ×ˢ ℘ (A ×ˢ A) ∧
      IsInternalWellOrder (kpair.π₂ p) (kpair.π₁ p)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = wellOrderCodes (v 1) ↔ _
  rw [mem_ext_iff]
  simp [wellOrderCodes]

theorem pair_mem_wellOrderCodes (A D R : V) :
    ⟨D, R⟩ₖ ∈ wellOrderCodes A ↔ D ⊆ A ∧ IsInternalWellOrder R D := by
  simp only [wellOrderCodes, mem_sep_iff, kpair_mem_iff, mem_power_iff,
    kpair.π₁_kpair, kpair.π₂_kpair]
  constructor
  · rintro ⟨⟨hD, _⟩, hR⟩
    exact ⟨hD, hR⟩
  · rintro ⟨hD, hR⟩
    refine ⟨⟨hD, ?_⟩, hR⟩
    intro p hp
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (hR.1 p hp)
    exact kpair_mem_iff.mpr ⟨hD x hx, hD y hy⟩

noncomputable def orderTypesOfSubsets (A : V) : V :=
  repl (fun p ↦ range (mostowskiMap (kpair.π₂ p) (kpair.π₁ p))) (by definability) (wellOrderCodes A)

theorem mem_orderTypesOfSubsets (A α : V) : α ∈ orderTypesOfSubsets A ↔
    ∃ D R, D ⊆ A ∧ IsInternalWellOrder R D ∧ internalOrderType R D = α := by
  rw [orderTypesOfSubsets, repl_spec]
  constructor
  · rintro ⟨p, hp, heq⟩
    obtain ⟨D, _, R, _, rfl⟩ := mem_prod_iff.mp ((mem_sep_iff.mp hp).1)
    have h := (pair_mem_wellOrderCodes A D R).mp hp
    exact ⟨D, R, h.1, h.2, by simpa [internalOrderType, eq_comm] using heq⟩
  · rintro ⟨D, R, hD, hR, heq⟩
    exact ⟨⟨D, R⟩ₖ, (pair_mem_wellOrderCodes A D R).mpr ⟨hD, hR⟩, by simpa [internalOrderType, eq_comm] using heq⟩

instance orderTypesOfSubsets_definable : ℒₛₑₜ-function₁[V] orderTypesOfSubsets := by
  have h : ℒₛₑₜ-relation (fun T A : V ↦ ∀ α, α ∈ T ↔
      ∃ D R, D ⊆ A ∧ IsInternalWellOrder R D ∧ internalOrderType R D = α) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = orderTypesOfSubsets (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_orderTypesOfSubsets]

theorem orderTypesOfSubsets_are_ordinals {A α : V} (hα : α ∈ orderTypesOfSubsets A) : IsOrdinal α := by
  obtain ⟨D, R, _, hR, rfl⟩ := (mem_orderTypesOfSubsets A α).mp hα
  exact internalOrderType_ordinal hR

noncomputable def orderTypeBound (A : V) : V := succ (⋃ˢ orderTypesOfSubsets A)

instance orderTypeBound_definable : ℒₛₑₜ-function₁[V] orderTypeBound := by
  unfold orderTypeBound
  definability

instance orderTypeBound_ordinal (A : V) : IsOrdinal (orderTypeBound A) := by
  have : IsOrdinal (⋃ˢ orderTypesOfSubsets A) := IsOrdinal.sUnion (fun _ h ↦ orderTypesOfSubsets_are_ordinals h)
  exact IsOrdinal.succ

theorem orderType_lt_bound {A R D : V} (hD : D ⊆ A) (hR : IsInternalWellOrder R D) :
    internalOrderType R D ∈ orderTypeBound A := by
  have hα : internalOrderType R D ∈ orderTypesOfSubsets A :=
    (mem_orderTypesOfSubsets A _).mpr ⟨D, R, hD, hR, rfl⟩
  have : IsOrdinal (internalOrderType R D) := internalOrderType_ordinal hR
  have : IsOrdinal (⋃ˢ orderTypesOfSubsets A) := IsOrdinal.sUnion (fun _ h ↦ orderTypesOfSubsets_are_ordinals h)
  exact mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (subset_sUnion_of_mem hα))

end ZFVP
