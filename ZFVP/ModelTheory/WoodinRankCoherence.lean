import ZFVP.ModelTheory.WoodinRankSuccessor
import ZFVP.ModelTheory.WoodinRecursionHistoryInduction
import ZFVP.ModelTheory.WoodinRecursionSuccessor
import ZFVP.SetTheory.ForcingBoundCodeExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingCodeExtends.rankStage_iff {θ η s z K J i : V}
    (h : ForcingCodeExtends s z) (hs : IsForcingIterationCode θ s)
    (hz : IsForcingIterationCode η z) (hK : IsIterationTable θ K)
    (hJ : IsIterationTable η J) (hKJ : K ⊆ J) (hi : i ∈ θ) :
    WoodinRankStage i s K ↔ WoodinRankStage i z J := by
  unfold WoodinRankStage
  rw [hs.tableP.value_of_subset hz.tableP h.subP hi,
    hs.tableR.value_of_subset hz.tableR h.subR hi,
    hs.tablet.value_of_subset hz.tablet h.subt hi,
    hK.value_of_subset hJ hKJ hi]

theorem woodinIterationRec_rankStage_previous {δ θ i : V} [IsOrdinal θ]
    (hs : ∀ j ∈ θ, IsWoodinIteration δ (succ j) (kpair.π₁ (woodinIterationRec j))
      (kpair.π₂ (woodinIterationRec j)))
    (hθ : IsWoodinIteration δ (succ θ) (kpair.π₁ (woodinIterationRec θ))
      (kpair.π₂ (woodinIterationRec θ))) (hi : i ∈ θ) :
    WoodinRankStage i (kpair.π₁ (woodinIterationRec i)) (kpair.π₂ (woodinIterationRec i)) ↔
      WoodinRankStage i (kpair.π₁ (woodinIterationRec θ)) (kpair.π₂ (woodinIterationRec θ)) := by
  have he := woodinIterationRec_extends_previous (woodinIterationHistory_of_stages hs) hi
  exact he.1.rankStage_iff (hs i hi).code hθ.code (hs i hi).cardinals hθ.cardinals
    he.2 (mem_succ_self i)

theorem woodinIterationRec_rankStage_successor [Countable V] {δ k : V} [IsOrdinal k]
    (hδ : IsWoodinSupercompact δ)
    (hs : ∀ j ∈ succ k, IsWoodinIteration δ (succ j) (kpair.π₁ (woodinIterationRec j))
      (kpair.π₂ (woodinIterationRec j)))
    (hr : WoodinRankStage k (kpair.π₁ (woodinIterationRec k)) (kpair.π₂ (woodinIterationRec k))) :
    WoodinRankStage (succ k) (kpair.π₁ (woodinIterationRec (succ k)))
      (kpair.π₂ (woodinIterationRec (succ k))) := by
  rw [woodinIterationRec_successor_of_history (woodinIterationHistory_of_stages hs)]
  simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using
    (hs k (mem_succ_self k)).successor_rankEnumerations hδ hr

end ZFVP
