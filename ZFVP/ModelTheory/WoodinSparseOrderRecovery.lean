import ZFVP.ModelTheory.WoodinSparseCarrierRecovery

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ i p q : V} [IsOrdinal θ]

theorem woodinSparseStageCode_order_restrict
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hi : i ∈ succ θ)
    (hp : p ∈ (forcingCodeP (woodinSparseStageCode i)) ‘ i)
    (hq : q ∈ (forcingCodeP (woodinSparseStageCode i)) ‘ i) :
    ⟨p, q⟩ₖ ∈ (forcingCodeR (woodinSparseStageCode θ)) ‘ θ ↔
      ⟨p, q⟩ₖ ∈ (forcingCodeR (woodinSparseStageCode i)) ‘ i := by
  let := IsOrdinal.of_mem hi
  rcases mem_succ_iff.mp hi with he | hi
  · subst i
    rfl
  have hi' := mem_succ_iff.mpr (Or.inr hi)
  have hpθ := woodinSparseStageCode_carrier_subset hΩ hAC hθ hi' p hp
  have hqi : q ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ i := by
    rwa [(woodinSparseStage_old_row hi').1]
  have hb := (woodinSparseStageCode_valid hΩ hAC hθ).system.order.below
    i hi' θ (mem_succ_self θ) (IsOrdinal.toIsTransitive.transitive _ hi) p hpθ q hqi
  rw [woodinSparseStageCode_section hΩ hAC hθ hi hqi,
    woodinSparseStageCode_projection hΩ hAC hθ hi hpθ,
    (woodinSparseStage_old_row hi').2] at hb
  have hsp := woodinSparseStageCode_sparse hΩ hAC
    (subset_trans (IsOrdinal.toIsTransitive.transitive _ hi) hθ) hp
  let := hsp.1
  rwa [IsFunction.restrict_eq_self p _ hsp.2.1] at hb

theorem woodinSparseStageCode_order_recovery
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hi : i ∈ succ θ) :
    (forcingCodeR (woodinSparseStageCode i)) ‘ i =
      ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) ∩
        (sparseCarrierCut ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) (succ (woodinSourceIndex i)) ×ˢ
         sparseCarrierCut ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) (succ (woodinSourceIndex i))) := by
  let := IsOrdinal.of_mem hi
  rw [← woodinSparseStageCode_carrier_recovery hΩ hAC hθ hi]
  have hsub := subset_trans (IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hi)) hθ
  have hR := (woodinSparseStageCode_valid hΩ hAC hsub).system.order.preorder i (mem_succ_self i)
  apply mem_ext
  intro z
  constructor
  · intro hz
    have hzP := hR.1 z hz
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hzP
    exact mem_inter_iff.mpr ⟨(woodinSparseStageCode_order_restrict hΩ hAC hθ hi hp hq).mpr hz, hzP⟩
  · intro hz
    obtain ⟨hzR, hzP⟩ := mem_inter_iff.mp hz
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hzP
    exact (woodinSparseStageCode_order_restrict hΩ hAC hθ hi hp hq).mp hzR

end ZFVP
