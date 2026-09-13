import ZFVP.ModelTheory.CriticalLimitVopenka

/-! Critical stages and their embeddings as objects inside the limit ZF model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CriticalSequence

variable {k : ℕ} {δ f κ : V} (hδ : Cn (k + 1) δ)
  (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
  (hκ : IsCriticalPoint (hierarchy δ) f κ)

include hδ h hκ

theorem limit_stage_cn {r : V} (hr : r ∈ (ω : V)) (m : ℕ)
    (α : SetDomain (hierarchy (criticalLimit f κ))) (hα : α.val = criticalIterate f κ r) :
    (cnFormula (m + 1)).Evalb ![α] := by
  have ho : IsOrdinal α.val := hα ▸ (iterate_spec hδ h hκ hr).1
  apply (limit_cn_iff_relative hδ h hκ m α ho).mpr
  rw [hα]
  exact (limit_elementaryInclusion hδ h hκ hr).relativeSigmaCorrect (m + 1)

variable [Nonempty (SetDomain (hierarchy (criticalLimit f κ)))]
  [(SetDomain (hierarchy (criticalLimit f κ)))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem stageEmbedding_internal {s t : V} (hs : s ∈ (ω : V)) (ht : t ∈ (ω : V))
    (α β e : SetDomain (hierarchy (criticalLimit f κ)))
    (hα : α.val = criticalIterate f κ s) (hβ : β.val = criticalIterate f κ t)
    (he : IsCodedMembershipEmbedding (hierarchy (criticalIterate f κ s))
      (hierarchy (criticalIterate f κ t)) e.val) :
    IsCodedMembershipEmbedding (hierarchy α) (hierarchy β) e := by
  let := limit_ordinal hδ h hκ
  let := hierarchy_transitive (criticalLimit f κ)
  have hoα := (TransitiveZF.ordinal_iff (hierarchy (criticalLimit f κ)) α).mpr
    (hα ▸ (iterate_spec hδ h hκ hs).1)
  have hoβ := (TransitiveZF.ordinal_iff (hierarchy (criticalLimit f κ)) β).mpr
    (hβ ▸ (iterate_spec hδ h hκ ht).1)
  apply TransitiveZF.embedding_of_embedding (hierarchy (criticalLimit f κ))
  rw [TransitiveZF.rankHierarchy_val (criticalLimit f κ) α hoα,
    TransitiveZF.rankHierarchy_val (criticalLimit f κ) β hoβ, hα, hβ]
  exact he

theorem stageCriticalPoint_internal {s t : V} (hs : s ∈ (ω : V)) (ht : t ∈ (ω : V))
    (α β e c : SetDomain (hierarchy (criticalLimit f κ)))
    (hα : α.val = criticalIterate f κ s) (hβ : β.val = criticalIterate f κ t)
    (he : IsCodedMembershipEmbedding (hierarchy (criticalIterate f κ s))
      (hierarchy (criticalIterate f κ t)) e.val)
    (hc : IsCriticalPoint (hierarchy (criticalIterate f κ s)) e.val c.val) :
    IsCriticalPoint (hierarchy α) e c := by
  let := limit_ordinal hδ h hκ
  let := hierarchy_transitive (criticalLimit f κ)
  have hoα := (TransitiveZF.ordinal_iff (hierarchy (criticalLimit f κ)) α).mpr
    (hα ▸ (iterate_spec hδ h hκ hs).1)
  let := hoα
  let := hierarchy_transitive α
  have hA := TransitiveZF.rankHierarchy_val (criticalLimit f κ) α hoα
  have htrans : IsTransitive (hierarchy α).val := by
    rw [hA, hα]
    let := (iterate_spec hδ h hκ hs).1
    exact hierarchy_transitive _
  let := htrans
  apply (TransitiveZF.criticalPoint_iff (hierarchy (criticalLimit f κ))
    (hierarchy α) (hierarchy β) e c (stageEmbedding_internal hδ h hκ hs ht α β e hα hβ he).function).mpr
  simpa only [hA, hα] using hc

end CriticalSequence

end ZFVP
