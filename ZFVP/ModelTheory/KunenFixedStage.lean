import ZFVP.ModelTheory.FixedStageSelfRestriction
import ZFVP.ModelTheory.KunenFromJonsson

/-! Kunen's contradiction at a fixed rank stage.

An embedding `f` of `hierarchy δ` into `hierarchy ε` that fixes an ordinal `η` above its critical
point restricts to a self-embedding of `hierarchy η`, with the same critical point and the same
critical sequence. Applying Kunen's argument to that restriction rules out an omega-Jonsson
function for the critical limit inside `hierarchy η`. This is the form the converse arguments of
Bagaria call. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- An embedding between rank stages that fixes a correct ordinal `η` above its critical point,
with the critical limit below `η`, admits no omega-Jonsson function for that limit in
`hierarchy η`. -/
theorem false_of_fixed_stage_embedding {k l m : ℕ} {δ ε f η κ : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε) (hηc : Cn (m + 1) η)
    (hm : omegaJonssonBound ≤ m + 1)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ)
    (hη : IsOrdinal η) (hηδ : η ∈ hierarchy δ) (hfix : f ‘ η = η) (hκη : κ ∈ η)
    (hlimη : criticalLimit f κ ∈ η)
    (hJ : ∃ F ∈ hierarchy η, IsOmegaJonsson F (criticalLimit f κ)) : False := by
  let := hη
  have hg : IsCodedMembershipEmbedding (hierarchy η) (hierarchy η) (f ↾ (hierarchy η)) :=
    selfRestriction_of_fixed_ordinal hδ hε h hκ hη hηδ hfix hκη
  have hκg : IsCriticalPoint (hierarchy η) (f ↾ (hierarchy η)) κ :=
    criticalPoint_selfRestriction hδ hε h hκ hη hηδ hfix hκη
  have heq : criticalLimit (f ↾ (hierarchy η)) κ = criticalLimit f κ :=
    criticalLimit_selfRestriction hδ hε h hκ hη hηδ hfix hκη
  let := CriticalSequence.limit_ordinal hηc hg hκg
  have hlim : criticalLimit (f ↾ (hierarchy η)) κ ∈ hierarchy η :=
    ordinal_mem_hierarchy_iff.mpr (by rw [heq]; exact hlimη)
  exact no_omegaJonsson_selfEmbedding hηc hm hg hκg hlim (by rw [heq]; exact hJ)

end ZFVP
