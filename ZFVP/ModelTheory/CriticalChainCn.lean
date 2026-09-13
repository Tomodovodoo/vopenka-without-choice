import ZFVP.ModelTheory.RelativeSigmaCorrectness

/-! Internal C(n) in the critical limit is characterized by relative correctness at a critical stage. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CriticalSequence

variable {k : ℕ} {δ f κ : V} (hδ : Cn (k + 1) δ)
  (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
  (hκ : IsCriticalPoint (hierarchy δ) f κ)

include hδ h hκ

theorem ordinal_mem_limit (μ : SetDomain (hierarchy (criticalLimit f κ))) (hμ : IsOrdinal μ.val) :
    μ.val ∈ criticalLimit f κ := by
  let := limit_ordinal hδ h hκ
  let := hμ
  simpa only [mem_hierarchy_iff_rank_mem, rank_of_ordinal] using μ.property

theorem limit_cn_iff_relative (m : ℕ) (μ : SetDomain (hierarchy (criticalLimit f κ)))
    (hμ : IsOrdinal μ.val) :
    (cnFormula (m + 1)).Evalb ![μ] ↔
      RelativeSigmaCorrect (m + 1) (hierarchy μ.val) (hierarchy (criticalLimit f κ)) := by
  let := limit_ordinal hδ h hκ
  let := hierarchy_transitive (criticalLimit f κ)
  let := rankDomain_nonempty (omega_mem_limit hδ h hκ)
  let := limit_models_zf hδ h hκ
  have hsub : hierarchy μ.val ⊆ hierarchy (criticalLimit f κ) :=
    (hierarchy_transitive (criticalLimit f κ)).transitive _ (hierarchy_mem (ordinal_mem_limit hδ h hκ μ hμ))
  exact (eval_cnFormula (m + 1) μ).trans (TransitiveZF.cn_iff_relative _ m μ hμ hsub)

theorem limit_cn_iff_stage (m : ℕ) (μ : SetDomain (hierarchy (criticalLimit f κ)))
    (hμ : IsOrdinal μ.val) {r : V} (hr : r ∈ (ω : V)) (hμr : μ.val ∈ criticalIterate f κ r) :
    (cnFormula (m + 1)).Evalb ![μ] ↔
      RelativeSigmaCorrect (m + 1) (hierarchy μ.val) (hierarchy (criticalIterate f κ r)) := by
  let := (iterate_spec hδ h hκ hr).1
  have hsub := (hierarchy_transitive (criticalIterate f κ r)).transitive _ (hierarchy_mem hμr)
  exact (limit_cn_iff_relative hδ h hκ m μ hμ).trans
    (relativeSigmaCorrect_elementary_target hsub (limit_elementaryInclusion hδ h hκ hr)).symm

theorem limit_cn_iff_exists_stage (m : ℕ) (μ : SetDomain (hierarchy (criticalLimit f κ)))
    (hμ : IsOrdinal μ.val) :
    (cnFormula (m + 1)).Evalb ![μ] ↔ ∃ r ∈ (ω : V), μ.val ∈ criticalIterate f κ r ∧
      RelativeSigmaCorrect (m + 1) (hierarchy μ.val) (hierarchy (criticalIterate f κ r)) := by
  constructor
  · intro hc
    obtain ⟨r, hr, hμr⟩ := (mem_criticalLimit_iff f κ μ.val).mp (ordinal_mem_limit hδ h hκ μ hμ)
    exact ⟨r, hr, hμr, (limit_cn_iff_stage hδ h hκ m μ hμ hr hμr).mp hc⟩
  · rintro ⟨r, hr, hμr, hc⟩
    exact (limit_cn_iff_stage hδ h hκ m μ hμ hr hμr).mpr hc

end CriticalSequence

end ZFVP
