import ZFVP.ModelTheory.CriticalSequenceFixedPoint
import ZFVP.ModelTheory.CriticalPointZF

/-! Every stage of the internal critical sequence satisfies the ZF rank criterion. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankEmbedding_rankCriterion_iff {k l : ℕ} {δ ε f α : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f) (hα : α ∈ hierarchy δ) :
    IsRankCriterionHeight α ↔ IsRankCriterionHeight (f ‘ α) := by
  let a : SetDomain (hierarchy δ) := ⟨α, hα⟩
  have hs := hδ.defined_correct (rankCriterionFormula_piOne.mono (by omega))
    (fun v ↦ IsRankCriterionHeight (v 0)) ![a]
  have ht := hε.defined_correct (rankCriterionFormula_piOne.mono (by omega))
    (fun v ↦ IsRankCriterionHeight (v 0)) (h.toFunction ∘ ![a])
  exact hs.symm.trans ((h.eval_semisentence rankCriterionFormula ![a]).trans ht)

namespace CriticalSequence

variable {k : ℕ} {δ f κ : V} (hδ : Cn (k + 1) δ)
  (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
  (hκ : IsCriticalPoint (hierarchy δ) f κ)

include hδ h hκ

theorem iterate_rankCriterion {n : V} (hn : n ∈ (ω : V)) :
    IsRankCriterionHeight (criticalIterate f κ n) := by
  have hall : ∀ n ∈ (ω : V), IsRankCriterionHeight (criticalIterate f κ n) := by
    apply naturalNumber_induction (fun n ↦ IsRankCriterionHeight (criticalIterate f κ n)) (by definability)
    · simpa using rankEmbedding_criticalPoint_rankCriterion hδ hδ h hκ
    · intro n hn ih
      rw [criticalIterate_succ f κ hn]
      exact (rankEmbedding_rankCriterion_iff hδ hδ h (iterate_spec hδ h hκ hn).2.1).mp ih
  exact hall n hn

theorem iterate_internalZFModel {n : V} (hn : n ∈ (ω : V)) :
    IsInternalZFModel (hierarchy (criticalIterate f κ n)) :=
  (iterate_rankCriterion hδ h hκ hn).internalZFModel

theorem iterate_models_zf {n : V} (hn : n ∈ (ω : V))
    [Nonempty (SetDomain (hierarchy (criticalIterate f κ n)))] :
    (SetDomain (hierarchy (criticalIterate f κ n)))↓[ℒₛₑₜ] ⊧* 𝗭𝗙 :=
  (iterate_rankCriterion hδ h hκ hn).models_zf

end CriticalSequence

end ZFVP
