import ZFVP.ModelTheory.LastPoint

/-! An ordinal mapped above the source bounds every fixed source ordinal. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankEmbedding_lastPoint_subset_moved {k l : ℕ} {θ η f γ : V}
    (hθ : Cn (k + 1) θ) (hη : Cn (l + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    (hγθ : γ ∈ θ) (hmove : θ ∈ f ‘ γ) : lastPoint θ f ⊆ γ := by
  let := hθ.ordinal
  let := hη.ordinal
  let : IsOrdinal γ := IsOrdinal.of_mem hγθ
  let := hierarchy_transitive θ
  let := hierarchy_transitive η
  have hγV := ordinal_subset_hierarchy θ γ hγθ
  let := hf.value_ordinal (show IsOrdinal γ from inferInstance) hγV
  intro β hβ
  obtain ⟨ξ, hξθ, hfix, hβξ⟩ := mem_lastPoint.mp hβ
  let : IsOrdinal ξ := IsOrdinal.of_mem hξθ
  have hξV := ordinal_subset_hierarchy θ ξ hξθ
  have hξγ : ξ ∈ γ := by
    rcases IsOrdinal.mem_trichotomy ξ γ with hl | he | hg
    · exact hl
    · have hm : θ ∈ ξ := by rwa [← he, hfix] at hmove
      exact False.elim (mem_asymm hξθ hm)
    · have hm := (hf.value_mem_iff hγV hξV).mpr hg
      rw [hfix] at hm
      have hh := IsOrdinal.toIsTransitive.mem_trans hmove hm
      exact False.elim (mem_asymm hξθ hh)
  exact IsOrdinal.toIsTransitive.mem_trans hβξ hξγ

end ZFVP
