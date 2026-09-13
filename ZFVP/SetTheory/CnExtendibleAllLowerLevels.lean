import ZFVP.SetTheory.CnExtendibleDownward
import ZFVP.SetTheory.ChoicelessInaccessible

/-! Positive extendibility implies every lower level, including level zero. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCnExtendible.zero {κ : V} (hκ : IsCnExtendible 1 κ) : IsCnExtendible 0 κ := by
  refine ⟨hκ.1, ?_⟩
  intro α hα hκα
  let : IsOrdinal α := hα
  let := hκ.1.1
  obtain ⟨μ, hαμ, hμ⟩ := cn_unbounded 1 α
  let := hμ.ordinal
  have hκμ := IsOrdinal.toIsTransitive.mem_trans hκα hαμ
  obtain ⟨θ, f, _, hθ, hf, hc, hμfκ⟩ := hκ.2 μ hμ hκμ
  let := hθ.ordinal
  let := hierarchy_transitive μ
  let := hierarchy_transitive θ
  let := hierarchy_transitive α
  have hαV := ordinal_subset_hierarchy μ α hαμ
  have hfα := hf.value_ordinal hα hαV
  let := hf.value_ordinal hc.ordinal hc.mem_domain
  have hαfκ := IsOrdinal.toIsTransitive.mem_trans hαμ hμfκ
  have hfκfα := (hf.value_mem_iff hc.mem_domain hαV).mpr hκα
  let := hfα
  have hαfα := IsOrdinal.toIsTransitive.mem_trans hαfκ hfκfα
  have hωα := IsOrdinal.toIsTransitive.mem_trans hκ.inaccessible.2.1 hκα
  have hr := rankEmbedding_restrict hμ hθ hf (hierarchy_mem hαμ)
    ⟨ω, ordinal_subset_hierarchy α _ hωα⟩
  rw [(rankEmbedding_value_hierarchy hμ hθ hf hα hαV).2] at hr
  have hcr := hc.restrict hf.function ((hierarchy_transitive μ).transitive _ (hierarchy_mem hαμ))
    (ordinal_subset_hierarchy α κ hκα)
  refine ⟨f ‘ α, f ↾ (hierarchy α), hαfα, hfα, hr, hcr, ?_⟩
  let := IsFunction.of_mem hf.function
  rw [value_restrict (by rw [domain_eq_of_mem_function hf.function]; exact hc.mem_domain)
    (ordinal_subset_hierarchy α κ hκα)]
  exact hαfκ

theorem IsCnExtendible.of_le_all {n N : ℕ} {κ : V}
    (hκ : IsCnExtendible N κ) (hN : 0 < N) (hn : n ≤ N) : IsCnExtendible n κ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  cases n with
  | zero => exact (hκ.of_le (Nat.zero_le k)).zero
  | succ n => exact hκ.of_le (by omega)

end ZFVP
