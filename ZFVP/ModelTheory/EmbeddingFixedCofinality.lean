import ZFVP.ModelTheory.EmbeddingCofinality

/-! An ordinal with a cofinal omega-sequence of fixed values is fixed. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankEmbedding_fixed_of_omegaCofinal {k l : ℕ} {θ η f μ g : V}
    (hθ : Cn (k + 1) θ) (hη : Cn (l + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    [IsOrdinal μ] (hμθ : μ ∈ θ) (hg : IsCofinalMap μ (ω : V) g)
    (hfix : ∀ i ∈ (ω : V), f ‘ (g ‘ i) = g ‘ i) : f ‘ μ = μ := by
  let := hθ.ordinal
  let := hη.ordinal
  let := hierarchy_transitive θ
  let := hierarchy_transitive η
  let : IsSequenceSupport (hierarchy θ) := ((cn_successor_iff k θ).mp hθ).2.support
  have hμV := ordinal_subset_hierarchy θ μ hμθ
  have hωV := ordinal_subset_hierarchy θ (ω : V) hθ.omega_lt
  have hgV := (hierarchy_transitive θ).mem_trans hg.1
    (function_mem_hierarchy_limit hθ.successor_closed hωV hμV)
  have hmap := hf.value_cofinalMap hgV hωV hμV hg
  rw [hf.value_omega hωV] at hmap
  let := hf.value_ordinal (show IsOrdinal μ from inferInstance) hμV
  apply SetTheory.subset_antisymm
  · intro β hβ
    let : IsOrdinal β := IsOrdinal.of_mem hβ
    obtain ⟨i, hi, hle⟩ := hmap.2 β hβ
    have hv := hf.value_apply hgV hωV (IsFunction.of_mem hg.1) (domain_eq_of_mem_function hg.1) hi
    rw [hf.value_natural hi, hfix i hi] at hv
    rw [hv] at hle
    let : IsOrdinal (g ‘ i) := IsOrdinal.of_mem (function_value_mem hg.1 hi)
    exact ordinal_mem_of_subset_mem hle (function_value_mem hg.1 hi)
  · exact hf.ordinal_subset_value inferInstance hμV

end ZFVP
