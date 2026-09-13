import ZFVP.ModelTheory.ModelEmbeddingHierarchy
import ZFVP.ModelTheory.CriticalChainCn
import ZFVP.ModelTheory.CriticalPointRestriction

/-! Embeddings between critical stages transport correctness inside the critical limit. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CriticalSequence

variable {k : ℕ} {δ f κ : V} (hδ : Cn (k + 1) δ)
  (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
  (hκ : IsCriticalPoint (hierarchy δ) f κ)

include hδ h hκ

theorem stageEmbedding_value_mem_limit {s t e μ : V} (hs : s ∈ (ω : V)) (ht : t ∈ (ω : V))
    (he : IsCodedMembershipEmbedding (hierarchy (criticalIterate f κ s))
      (hierarchy (criticalIterate f κ t)) e) (hμ : μ ∈ criticalIterate f κ s) :
    e ‘ μ ∈ hierarchy (criticalLimit f κ) := by
  let := (iterate_spec hδ h hκ hs).1
  let := limit_ordinal hδ h hκ
  exact (hierarchy_transitive (criticalLimit f κ)).mem_trans
    (function_value_mem he.function (ordinal_subset_hierarchy _ _ hμ))
    (hierarchy_mem (iterate_mem_limit hδ h hκ ht))

theorem stageEmbedding_cn {s t r u e : V}
    (hs : s ∈ (ω : V)) (ht : t ∈ (ω : V)) (hr : r ∈ (ω : V)) (hu : u ∈ (ω : V))
    (he : IsCodedMembershipEmbedding (hierarchy (criticalIterate f κ s))
      (hierarchy (criticalIterate f κ t)) e)
    (hrs : criticalIterate f κ r ∈ criticalIterate f κ s)
    (hru : e ‘ (criticalIterate f κ r) = criticalIterate f κ u)
    (m : ℕ) (μ ν : SetDomain (hierarchy (criticalLimit f κ)))
    (hμ : IsOrdinal μ.val) (hμr : μ.val ∈ criticalIterate f κ r) (hν : ν.val = e ‘ μ.val) :
    (cnFormula (m + 1)).Evalb ![μ] ↔ (cnFormula (m + 1)).Evalb ![ν] := by
  let := (iterate_spec hδ h hκ hs).1
  let := (iterate_spec hδ h hκ ht).1
  let := (iterate_spec hδ h hκ hr).1
  let := hierarchy_transitive (criticalIterate f κ s)
  let := hierarchy_transitive (criticalIterate f κ t)
  let := rankDomain_nonempty (iterate_rankCriterion hδ h hκ hs).2.1
  let := rankDomain_nonempty (iterate_rankCriterion hδ h hκ ht).2.1
  let := iterate_models_zf hδ h hκ hs
  let := iterate_models_zf hδ h hκ ht
  have hμs := IsOrdinal.toIsTransitive.mem_trans hμr hrs
  have hμV := ordinal_subset_hierarchy (criticalIterate f κ s) μ.val hμs
  have hrV := ordinal_subset_hierarchy (criticalIterate f κ s) _ hrs
  have hνord : IsOrdinal ν.val := hν ▸ he.value_ordinal hμ hμV
  have hνu : ν.val ∈ criticalIterate f κ u := by
    rw [hν, ← hru]
    exact (he.value_mem_iff hμV hrV).mpr hμr
  have hc := modelEmbedding_relativeSigmaCorrect_iff he (m + 1) (hierarchy_mem hμs) (hierarchy_mem hrs)
  rw [(modelEmbedding_value_hierarchy he hμ hμV).2,
    (modelEmbedding_value_hierarchy he (iterate_spec hδ h hκ hr).1 hrV).2, hru, ← hν] at hc
  exact (limit_cn_iff_stage hδ h hκ m μ hμ hr hμr).trans
    (hc.trans (limit_cn_iff_stage hδ h hκ m ν hνord hu hνu).symm)

theorem stageEmbedding_restrict {s t e μ : V} (hs : s ∈ (ω : V)) (ht : t ∈ (ω : V))
    (he : IsCodedMembershipEmbedding (hierarchy (criticalIterate f κ s))
      (hierarchy (criticalIterate f κ t)) e)
    (hμ : IsOrdinal μ) (hμs : μ ∈ criticalIterate f κ s) (hne : IsNonempty (hierarchy μ)) :
    IsOrdinal (e ‘ μ) ∧ e ‘ μ ∈ criticalLimit f κ ∧
      IsCodedMembershipEmbedding (hierarchy μ) (hierarchy (e ‘ μ)) (e ↾ (hierarchy μ)) ∧
      e ↾ (hierarchy μ) ∈ hierarchy (criticalLimit f κ) := by
  let := (iterate_spec hδ h hκ hs).1
  let := (iterate_spec hδ h hκ ht).1
  let := hierarchy_transitive (criticalIterate f κ s)
  let := hierarchy_transitive (criticalIterate f κ t)
  let := rankDomain_nonempty (iterate_rankCriterion hδ h hκ hs).2.1
  let := rankDomain_nonempty (iterate_rankCriterion hδ h hκ ht).2.1
  let := iterate_models_zf hδ h hκ hs
  let := iterate_models_zf hδ h hκ ht
  let := limit_ordinal hδ h hκ
  have hμV := ordinal_subset_hierarchy (criticalIterate f κ s) μ hμs
  obtain ⟨hν, hv⟩ := modelEmbedding_value_hierarchy he hμ hμV
  let := hν
  have hνlim : e ‘ μ ∈ criticalLimit f κ := by
    exact ordinal_mem_hierarchy_iff.mp (stageEmbedding_value_mem_limit hδ h hκ hs ht he hμs)
  have her := modelEmbedding_restrict he (hierarchy_mem hμs) hne
  rw [hv] at her
  refine ⟨hν, hνlim, her, ?_⟩
  have hμlim := IsOrdinal.toIsTransitive.mem_trans hμs (iterate_mem_limit hδ h hκ hs)
  exact (hierarchy_transitive (criticalLimit f κ)).mem_trans her.function
    (function_mem_hierarchy_limit (fun _ ↦ limit_succ_closed hδ h hκ)
      (hierarchy_mem hμlim) (hierarchy_mem hνlim))

end CriticalSequence

end ZFVP
