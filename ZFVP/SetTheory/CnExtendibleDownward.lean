import ZFVP.ModelTheory.EmbeddingCnTransfer
import ZFVP.ModelTheory.CriticalPointRestriction

/-! Positive C(n)-extendibility decreases with the correctness level, in ZF. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCnExtendible.predecessor {n : ℕ} {κ : V} (hκ : IsCnExtendible (n + 2) κ) :
    IsCnExtendible (n + 1) κ := by
  refine ⟨hκ.1, ?_⟩
  intro α hα hκα
  let := hα.ordinal
  obtain ⟨μ, hαμ, hμ⟩ := cn_unbounded (n + 2) α
  let := hμ.ordinal
  have hκμ := IsOrdinal.toIsTransitive.mem_trans hκα hαμ
  obtain ⟨θ, f, _, hθ, hf, hc, hμfκ⟩ := hκ.2 μ hμ hκμ
  let := hθ.ordinal
  let := hierarchy_transitive μ
  let := hierarchy_transitive θ
  let := hierarchy_transitive α
  have hαV := ordinal_subset_hierarchy μ α hαμ
  have hκαV := ordinal_subset_hierarchy α κ hκα
  have hκV := hc.mem_domain
  have hCn := (rankEmbedding_cn_iff hμ hθ hf hαV).mp hα
  let := hCn.ordinal
  let := hf.value_ordinal hc.ordinal hκV
  have hαfκ := IsOrdinal.toIsTransitive.mem_trans hαμ hμfκ
  have hfκfα := (hf.value_mem_iff hκV hαV).mpr hκα
  have hαfα := IsOrdinal.toIsTransitive.mem_trans hαfκ hfκfα
  have hr := rankEmbedding_restrict hμ hθ hf (hierarchy_mem hαμ)
    ⟨ω, ordinal_subset_hierarchy α _ hα.omega_lt⟩
  rw [(rankEmbedding_value_hierarchy hμ hθ hf hα.ordinal hαV).2] at hr
  have hcr := hc.restrict hf.function ((hierarchy_transitive μ).transitive _ (hierarchy_mem hαμ)) hκαV
  refine ⟨f ‘ α, f ↾ (hierarchy α), hαfα, hCn, hr, hcr, ?_⟩
  let := IsFunction.of_mem hf.function
  rw [value_restrict (by rw [domain_eq_of_mem_function hf.function]; exact hκV) hκαV]
  exact hαfκ

theorem IsCnExtendible.of_le {n m : ℕ} {κ : V} (hκ : IsCnExtendible (m + 1) κ) (hnm : n ≤ m) :
    IsCnExtendible (n + 1) κ := by
  induction m, hnm using Nat.le_induction with
  | base => exact hκ
  | succ m hnm ih => exact ih hκ.predecessor

end ZFVP
