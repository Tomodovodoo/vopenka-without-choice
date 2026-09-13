import ZFVP.SetTheory.EndExtensionLevyCollapse
import ZFVP.SetTheory.EndExtensionRegular
import ZFVP.SetTheory.LevyColumnSplitting
import ZFVP.ModelTheory.SubposetRealization

/-! Column collapses, restricted orders and injections are absolute for membership end
extensions; the upper collapse is the column collapse on `κ \ β`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V W : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace MembershipEndExtension

variable (j : MembershipEndExtension V W)

theorem map_restrictedOrder (R Q : V) : j (restrictedOrder R Q) = restrictedOrder (j R) (j Q) := by
  unfold restrictedOrder
  rw [j.map_inter, j.map_prod]

theorem map_levyColumns (κ C : V) : j (levyColumns κ C) = levyColumns (j κ) (j C) := by
  unfold levyColumns
  rw [j.map_separation _ (fun p ↦ levyCut C p = p) (fun p ↦ levyCut (j C) p = p)
    (by unfold levyCut; definability) (by unfold levyCut; definability), j.map_levyCollapse]
  intro p _
  rw [← j.map_levyCut]
  exact ⟨fun h ↦ by rw [h], fun h ↦ j.injective h⟩

theorem map_levyColumnsOrder (κ C : V) : j (levyColumnsOrder κ C) = levyColumnsOrder (j κ) (j C) := by
  unfold levyColumnsOrder
  rw [j.map_reverseInclusionOrder, j.map_levyColumns]

end MembershipEndExtension

/-- The upper collapse is the column collapse on the columns `κ \ β`. -/
theorem levyCollapseAbove_eq_levyColumns (κ β : V) : levyCollapseAbove κ β = levyColumns κ (κ \ β) := by
  apply mem_ext
  intro p
  rw [mem_levyCollapseAbove_iff, mem_levyColumns_iff]
  apply and_congr_right
  intro hp
  constructor
  · intro hcut
    apply SetTheory.subset_antisymm (levyCut_subset _ _)
    intro z hz
    obtain ⟨n, α, γ, hn, hα, rfl⟩ := levyCollapse_mem_shape hp hz
    refine (kpair_mem_levyCut_iff _ _ _ _).mpr ⟨hz, kpair_mem_iff.mpr ⟨hn, mem_sdiff_iff.mpr ⟨hα, ?_⟩⟩⟩
    intro hαβ
    have : ⟨⟨n, α⟩ₖ, γ⟩ₖ ∈ levyCut β p := (kpair_mem_levyCut_iff _ _ _ _).mpr ⟨hz, kpair_mem_iff.mpr ⟨hn, hαβ⟩⟩
    rw [hcut] at this
    exact not_mem_empty this
  · intro hcol
    apply mem_ext
    intro z
    constructor
    · intro hz
      obtain ⟨hzp, x, hxω, y, rfl⟩ := mem_restrict_iff.mp hz
      obtain ⟨n, α, γ, hn, hα, he⟩ := levyCollapse_mem_shape hp hzp
      obtain ⟨hx, _⟩ := kpair_iff.mp he
      rw [hx] at hxω
      have hzcol : ⟨x, y⟩ₖ ∈ levyCut (κ \ β) p := by rw [hcol]; exact hzp
      have h1 := (kpair_mem_levyCut_iff _ _ _ _).mp hzcol
      rw [hx] at h1
      have h2 := (kpair_mem_iff.mp h1.2).2
      exact ((mem_sdiff_iff.mp h2).2 (kpair_mem_iff.mp hxω).2).elim
    · intro hz
      exact (not_mem_empty hz).elim

end ZFVP
