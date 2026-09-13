import ZFVP.ModelTheory.WoodinSparseCarrierRecovery
import ZFVP.ModelTheory.WoodinSparseCodeCompatibility
import ZFVP.ModelTheory.WoodinSparseOwnRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]

theorem woodinSparseStageCode_direct_mem_iff_earlier
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) (p : V) :
    p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ ↔
      ∃ i ∈ θ, p ∈ (forcingCodeP (woodinSparseStageCode i)) ‘ i := by
  constructor
  · intro hp
    have hp' := hp
    rw [(woodinSparseStageCode_direct h0 hlim hinac).1] at hp'
    obtain ⟨_, i, hi, hd⟩ := mem_woodinSparseDirectBase_iff.mp hp'
    refine ⟨i, hi, ?_⟩
    rw [woodinSparseStageCode_carrier_recovery hΩ hAC hθ (mem_succ_iff.mpr (Or.inr hi))]
    exact mem_sparseCarrierCut_iff.mpr ⟨hp, hd⟩
  · rintro ⟨i, hi, hp⟩
    exact woodinSparseStageCode_carrier_subset hΩ hAC hθ (mem_succ_iff.mpr (Or.inr hi)) p hp

theorem woodinSparseStageCode_limit_rank_lower
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (ih : ∀ i ∈ θ, (kpair.π₂ (woodinIterationRec i)) ‘ i ⊆
      rank ((forcingCodeP (woodinSparseStageCode i)) ‘ i)) :
    θ ⊆ rank ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) := by
  have hs := woodinIterationPrefix_of_stages
    (fun i hi ↦ ((woodinIterationExit hΩ hAC).2.1 i (hθ i hi)).1)
  intro β hβ
  obtain ⟨i, hi, hβi⟩ := hs.limitCardinal_cofinal (hs.index_subset_limit hlim β hβ)
  rw [woodinIterationCardinalPrefix_value hΩ hAC hθ hi] at hβi
  exact rank_mono (woodinSparseStageCode_carrier_subset hΩ hAC hθ (mem_succ_iff.mpr (Or.inr hi))) β
    (ih i hi β hβi)

end ZFVP
