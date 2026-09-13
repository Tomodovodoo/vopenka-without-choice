import ZFVP.ModelTheory.CriticalPoint

/-! The supremum of the fixed ordinals of a rank embedding. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def fixedOrdinals (θ f : V) : V := {ξ ∈ θ ; f ‘ ξ = ξ}

instance fixedOrdinals_definable : ℒₛₑₜ-function₂[V] fixedOrdinals := by
  apply Language.Definable.of_iff (show ℒₛₑₜ-relation₃[V]
    (fun X θ f ↦ ∀ ξ, ξ ∈ X ↔ ξ ∈ θ ∧ f ‘ ξ = ξ) from by definability)
  intro v
  rw [mem_ext_iff]
  simp [fixedOrdinals]

@[simp] theorem mem_fixedOrdinals {θ f ξ : V} : ξ ∈ fixedOrdinals θ f ↔ ξ ∈ θ ∧ f ‘ ξ = ξ := by
  simp [fixedOrdinals]

noncomputable def lastPoint (θ f : V) : V := ⋃ˢ (fixedOrdinals θ f)

instance lastPoint_definable : ℒₛₑₜ-function₂[V] lastPoint := by
  unfold lastPoint
  definability

theorem lastPoint_ordinal (θ f : V) [IsOrdinal θ] : IsOrdinal (lastPoint θ f) :=
  IsOrdinal.sUnion (fun _ h ↦ IsOrdinal.of_mem (mem_fixedOrdinals.mp h).1)

theorem mem_lastPoint {θ f β : V} : β ∈ lastPoint θ f ↔ ∃ ξ ∈ θ, f ‘ ξ = ξ ∧ β ∈ ξ := by
  simp only [lastPoint, mem_sUnion_iff, mem_fixedOrdinals]
  aesop

theorem lastPoint_subset (θ f : V) [IsOrdinal θ] : lastPoint θ f ⊆ θ := by
  intro β hβ
  obtain ⟨ξ, hξ, _, hβξ⟩ := mem_lastPoint.mp hβ
  exact IsOrdinal.toIsTransitive.mem_trans hβξ hξ

theorem rankEmbedding_fixed_mem_lastPoint {k l : ℕ} {θ η f ξ : V}
    (hθ : Cn (k + 1) θ) (hη : Cn (l + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    (hξ : ξ ∈ θ) (hfix : f ‘ ξ = ξ) : ξ ∈ lastPoint θ f := by
  let := hθ.ordinal
  let := hη.ordinal
  let := hierarchy_transitive θ
  let := hierarchy_transitive η
  have hs : succ ξ ∈ θ := hθ.successor_closed ξ hξ
  apply mem_lastPoint.mpr
  refine ⟨succ ξ, hs, ?_, by simp⟩
  rw [hf.value_succ (ordinal_subset_hierarchy θ ξ hξ)
    (ordinal_subset_hierarchy θ (succ ξ) hs), hfix]

theorem rankEmbedding_fixed_cofinal_lastPoint {k l : ℕ} {θ η f β : V}
    (hθ : Cn (k + 1) θ) (hη : Cn (l + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    (hβ : β ∈ lastPoint θ f) : ∃ ξ ∈ lastPoint θ f, β ∈ ξ ∧ f ‘ ξ = ξ := by
  obtain ⟨ξ, hξ, hfix, hβξ⟩ := mem_lastPoint.mp hβ
  exact ⟨ξ, rankEmbedding_fixed_mem_lastPoint hθ hη hf hξ hfix, hβξ, hfix⟩

theorem IsCriticalPoint.subset_lastPoint {k l : ℕ} {θ η f κ : V}
    (hc : IsCriticalPoint (hierarchy θ) f κ)
    (hθ : Cn (k + 1) θ) (hη : Cn (l + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f) : κ ⊆ lastPoint θ f := by
  let := hθ.ordinal
  let := hc.ordinal
  let := hierarchy_transitive θ
  intro ξ hξ
  have hξθ := IsOrdinal.toIsTransitive.mem_trans hξ (ordinal_mem_hierarchy_iff.mp hc.mem_domain)
  exact rankEmbedding_fixed_mem_lastPoint hθ hη hf hξθ (hc.fixed_below hξ)

theorem rankEmbedding_lastPoint_lt_image {k l : ℕ} {θ η f : V}
    (hθ : Cn (k + 1) θ) (hη : Cn (l + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    (hγ : lastPoint θ f ∈ θ) : lastPoint θ f ∈ f ‘ (lastPoint θ f) := by
  let := hθ.ordinal
  let := hη.ordinal
  let := hierarchy_transitive θ
  let := hierarchy_transitive η
  let := lastPoint_ordinal θ f
  have hV := ordinal_subset_hierarchy θ (lastPoint θ f) hγ
  let := hf.value_ordinal (lastPoint_ordinal θ f) hV
  rcases IsOrdinal.subset_iff.mp (hf.ordinal_subset_value (lastPoint_ordinal θ f) hV) with he | hl
  · exact False.elim (mem_irrefl (lastPoint θ f)
      (rankEmbedding_fixed_mem_lastPoint hθ hη hf hγ he.symm))
  · exact hl

theorem rankEmbedding_height_subset {k l : ℕ} {θ η f : V}
    (hθ : Cn (k + 1) θ) (hη : Cn (l + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f) : θ ⊆ η := by
  let := hθ.ordinal
  let := hη.ordinal
  let := hierarchy_transitive θ
  let := hierarchy_transitive η
  intro ξ hξ
  let : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have hV := ordinal_subset_hierarchy θ ξ hξ
  let := hf.value_ordinal (show IsOrdinal ξ from inferInstance) hV
  exact ordinal_mem_of_subset_mem (hf.ordinal_subset_value inferInstance hV)
    (ordinal_mem_hierarchy_iff.mp (function_value_mem hf.function hV))

theorem rankEmbedding_above_lastPoint_lt_image {k l : ℕ} {θ η f ξ : V}
    (hθ : Cn (k + 1) θ) (hη : Cn (l + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    (hξ : ξ ∈ θ) (hγξ : lastPoint θ f ⊆ ξ) : ξ ∈ f ‘ ξ := by
  let := hθ.ordinal
  let := hη.ordinal
  let : IsOrdinal ξ := IsOrdinal.of_mem hξ
  let := hierarchy_transitive θ
  let := hierarchy_transitive η
  have hV := ordinal_subset_hierarchy θ ξ hξ
  let := hf.value_ordinal (show IsOrdinal ξ from inferInstance) hV
  rcases IsOrdinal.subset_iff.mp (hf.ordinal_subset_value (show IsOrdinal ξ from inferInstance) hV)
    with he | hl
  · have hh := rankEmbedding_fixed_mem_lastPoint hθ hη hf hξ he.symm
    exact False.elim (mem_irrefl ξ (hγξ ξ hh))
  · exact hl

end ZFVP
