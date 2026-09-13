import ZFVP.SetTheory.LevyUpperPermutations
import ZFVP.SetTheory.LevyColumnSplitting
import ZFVP.SetTheory.MeasurableStrongLimit
import ZFVP.SetTheory.Hessenberg

/-! The full Levy collapse as the upper collapse above `∅`: it is weakly homogeneous; the columns
below `β` form the collapse `Coll(ω, <β)`; and below a measurable the collapse `Coll(ω, <β)` is
small. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem levyCut_empty_left (p : V) : levyCut (∅ : V) p = ∅ := by
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨_, x, hx, _, _⟩ := mem_restrict_iff.mp hz
    obtain ⟨_, _, y, hy, _⟩ := mem_prod_iff.mp hx
    exact (not_mem_empty hy).elim
  · intro hz
    exact (not_mem_empty hz).elim

theorem levyCollapseAbove_empty (κ : V) : levyCollapseAbove κ ∅ = levyCollapse κ := by
  apply mem_ext
  intro p
  rw [mem_levyCollapseAbove_iff]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, levyCut_empty_left p⟩⟩

theorem restrictedOrder_levyOrder (κ : V) : restrictedOrder (levyOrder κ) (levyCollapse κ) = levyOrder κ := by
  apply mem_ext
  intro z
  unfold restrictedOrder
  rw [mem_inter_iff]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, (reverseInclusionOrder_poset (levyCollapse κ)).1.1 z h⟩⟩

/-- The full Levy collapse is weakly homogeneous. -/
theorem levyCollapse_homogeneous (κ : V) : IsWeaklyHomogeneous (levyCollapse κ) (levyOrder κ) ∅ := by
  have h := levyCollapseAbove_homogeneous (κ := κ) (β := ∅) (empty_subset κ)
  rwa [levyCollapseAbove_empty, restrictedOrder_levyOrder] at h

/-- The columns below `β` form the collapse `Coll(ω, <β)`. -/
theorem levyColumns_eq_levyCollapse {κ β : V} [IsOrdinal β] (hβ : β ⊆ κ) :
    levyColumns κ β = levyCollapse β := by
  apply mem_ext
  intro p
  rw [mem_levyColumns_iff]
  constructor
  · rintro ⟨hp, hcut⟩
    have hpf : IsFunction p := ((mem_finitePartialFunctions _ _ _).mp (mem_sep_iff.mp hp).1).2.1
    have hfin := ((mem_finitePartialFunctions _ _ _).mp (mem_sep_iff.mp hp).1).2.2
    refine mem_sep_iff.mpr ⟨(mem_finitePartialFunctions _ _ _).mpr ⟨?_, hpf, hfin⟩, (mem_sep_iff.mp hp).2⟩
    intro z hz
    obtain ⟨n, α, γ, hn, _, rfl⟩ := levyCollapse_mem_shape hp hz
    have hγ : γ ∈ α := ((mem_levyCollapse_iff κ p).mp hp).2 n α γ hz
    have hz' : ⟨⟨n, α⟩ₖ, γ⟩ₖ ∈ levyCut β p := by rw [hcut]; exact hz
    obtain ⟨_, hnα⟩ := (kpair_mem_levyCut_iff _ _ _ _).mp hz'
    have hαβ : α ∈ β := (kpair_mem_iff.mp hnα).2
    exact kpair_mem_iff.mpr ⟨kpair_mem_iff.mpr ⟨hn, hαβ⟩, IsOrdinal.toIsTransitive.mem_trans hγ hαβ⟩
  · intro hp
    refine ⟨levyCollapse_mono hβ p hp, ?_⟩
    have hpf : IsFunction p := ((mem_finitePartialFunctions _ _ _).mp (mem_sep_iff.mp hp).1).2.1
    have hsub : p ⊆ ((ω : V) ×ˢ β) ×ˢ β := ((mem_finitePartialFunctions _ _ _).mp (mem_sep_iff.mp hp).1).1
    unfold levyCut
    apply IsFunction.restrict_eq_self
    intro x hx
    obtain ⟨y, hy⟩ := mem_domain_iff.mp hx
    exact (kpair_mem_iff.mp (hsub _ hy)).1

theorem levyCollapse_subset_power (β : V) : levyCollapse β ⊆ ℘ (((ω : V) ×ˢ β) ×ˢ β) :=
  fun p hp ↦ mem_power_iff.mpr ((mem_finitePartialFunctions _ _ _).mp (mem_sep_iff.mp hp).1).1

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U) (hω : (ω : V) ∈ κ)

include hAC hU hc hω in
/-- Below a measurable, `Coll(ω, <β)` is small. -/
theorem levyCollapse_cardLE_small {β : V} (hβ : β ∈ κ) : ∃ ν ∈ κ, levyCollapse β ≤# ν := by
  have : IsOrdinal β := IsOrdinal.of_mem hβ
  obtain ⟨μ, hμdef⟩ : ∃ μ : V, μ = β ∪ (ω : V) := ⟨_, rfl⟩
  have : IsOrdinal μ := hμdef ▸ ordinal_union_isOrdinal β (ω : V)
  have hμκ : μ ∈ κ := hμdef ▸ union_mem_of_ordinals hβ hω
  have hβμ : β ⊆ μ := hμdef ▸ subset_union_left _ _
  have hωμ : (ω : V) ⊆ μ := hμdef ▸ subset_union_right _ _
  have hμμ : μ ∪ (ω : V) = μ := by
    apply SetTheory.subset_antisymm
    · intro z hz
      rcases mem_union_iff.mp hz with h | h
      · exact h
      · exact hωμ z h
    · exact subset_union_left _ _
  have h1 : (ω : V) ×ˢ β ≤# μ := by
    refine CardLE.trans (cardLE_of_subset ?_) ((ordinal_prod_cardLE_union_omega μ).trans (by rw [hμμ]))
    intro z hz
    obtain ⟨n, hn, b, hb, rfl⟩ := mem_prod_iff.mp hz
    exact kpair_mem_iff.mpr ⟨hωμ n hn, hβμ b hb⟩
  have h2 : ((ω : V) ×ˢ β) ×ˢ β ≤# μ :=
    (prod_cardLE_prod h1 (cardLE_of_subset hβμ)).trans ((ordinal_prod_cardLE_union_omega μ).trans (by rw [hμμ]))
  obtain ⟨ν, hν, hpow⟩ := power_small_of_measurable hAC hU hc hμκ h2
  exact ⟨ν, hν, (cardLE_of_subset (levyCollapse_subset_power β)).trans hpow⟩

end

end ZFVP
