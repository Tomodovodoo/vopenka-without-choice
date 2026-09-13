import ZFVP.ModelTheory.EmbeddingCofinality
import ZFVP.SetTheory.PiOneRankCriterion

/-! The critical point satisfies the ZF rank criterion. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCriticalPoint.succ_closed {A B f κ α : V} [IsTransitive A] [IsTransitive B]
    (hκ : IsCriticalPoint A f κ) (h : IsCodedMembershipEmbedding A B f) (hα : α ∈ κ) :
    succ α ∈ κ := by
  let := hκ.ordinal
  let := IsOrdinal.of_mem hα
  have hs : succ α ⊆ κ := by
    intro x hx
    rcases mem_succ_iff.mp hx with rfl | hx
    · exact hα
    · exact IsOrdinal.toIsTransitive.mem_trans hx hα
  rcases IsOrdinal.subset_iff.mp hs with he | hl
  · have haA := (inferInstance : IsTransitive A).mem_trans hα hκ.mem_domain
    have hv := h.value_succ haA (he.symm ▸ hκ.mem_domain)
    rw [he, hκ.fixed_below hα] at hv
    exact False.elim (hκ.moved (hv.trans he))
  · exact hl

theorem rankEmbedding_criticalPoint_noLowRankCofinalMaps {k l : ℕ} {δ ε f κ : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) : NoLowRankCofinalMaps κ :=
  fun _ ha _ ↦ rankEmbedding_criticalPoint_no_cofinalMap hδ hε h hκ ha

theorem rankEmbedding_criticalPoint_models_zf {k l : ℕ} {δ ε f κ : V}
    [Nonempty (SetDomain (hierarchy κ))]
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) :
    (SetDomain (hierarchy κ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  let := hκ.ordinal
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff k δ).mp hδ).2.support
  let : IsSequenceSupport (hierarchy ε) := ((cn_successor_iff l ε).mp hε).2.support
  exact rankDomain_models_zf (hκ.omega_lt h) (fun _ ha ↦ hκ.succ_closed h ha)
    (rankEmbedding_criticalPoint_noLowRankCofinalMaps hδ hε h hκ)

theorem rankEmbedding_criticalPoint_rankCriterion {k l : ℕ} {δ ε f κ : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) : IsRankCriterionHeight κ := by
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff k δ).mp hδ).2.support
  let : IsSequenceSupport (hierarchy ε) := ((cn_successor_iff l ε).mp hε).2.support
  exact ⟨hκ.ordinal, hκ.omega_lt h, fun _ ha ↦ hκ.succ_closed h ha,
    rankEmbedding_criticalPoint_noLowRankCofinalMaps hδ hε h hκ⟩

theorem rankEmbedding_criticalPoint_internalZFModel {k l : ℕ} {δ ε f κ : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) : IsInternalZFModel (hierarchy κ) :=
  (rankEmbedding_criticalPoint_rankCriterion hδ hε h hκ).internalZFModel

end ZFVP
