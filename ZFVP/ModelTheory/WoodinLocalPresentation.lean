import ZFVP.ModelTheory.WoodinLocalStageOrder
import ZFVP.ModelTheory.WoodinEndpointLocalCarrier

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The local comparison relation restricted to a given carrier. -/
noncomputable def woodinLocalOrderOn (C : V) : V :=
  {a ∈ C ×ˢ C ; WoodinLocalStageOrder (kpair.π₁ a) (kpair.π₂ a)}

theorem mem_woodinLocalOrderOn_iff (C z w : V) :
    ⟨z, w⟩ₖ ∈ woodinLocalOrderOn C ↔ z ∈ C ∧ w ∈ C ∧ WoodinLocalStageOrder z w := by
  unfold woodinLocalOrderOn WoodinLocalStageOrder
  rw [mem_sep_iff]
  simp only [kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  tauto

noncomputable def woodinStageCarrier (θ : V) : V :=
  forcingStageConditions θ (forcingCodeP (woodinIterationPrefix θ))
    (forcingCodeUniverse (woodinIterationPrefix θ))

noncomputable def woodinStageMap (θ : V) : V :=
  forcingStageThreadMap θ (forcingCodeP (woodinIterationPrefix θ))
    (forcingCodeπ (woodinIterationPrefix θ)) (forcingCodeE (woodinIterationPrefix θ))
    (forcingCodeUniverse (woodinIterationPrefix θ))

variable {δ θ : V} [IsOrdinal θ]
  (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
    (kpair.π₂ (woodinIterationRec k)))
include hs

theorem woodinLocalOrderOn_eq_pullback :
    woodinLocalOrderOn (woodinStageCarrier θ) =
      forcingPullbackOrder (woodinStageCarrier θ)
        (forcingThreadOrder θ (forcingCodeR (woodinIterationPrefix θ))
          (forcingDirectLimit θ (forcingCodeP (woodinIterationPrefix θ))
            (forcingCodeπ (woodinIterationPrefix θ)) (forcingCodeE (woodinIterationPrefix θ))
            (forcingCodeUniverse (woodinIterationPrefix θ)))) (woodinStageMap θ) := by
  apply SetTheory.subset_antisymm
  · intro a ha
    obtain ⟨z, hz, w, hw, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp ha).1
    exact (woodinStagePullback_order_iff hs hz hw).mpr
      ((mem_woodinLocalOrderOn_iff _ _ _).mp ha).2.2
  · intro a ha
    obtain ⟨z, hz, w, hw, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp ha).1
    exact (mem_woodinLocalOrderOn_iff _ _ _).mpr
      ⟨hz, hw, (woodinStagePullback_order_iff hs hz hw).mp ha⟩

theorem woodinLocalOrderOn_preorder :
    IsForcingPreorder (woodinStageCarrier θ) (woodinLocalOrderOn (woodinStageCarrier θ)) := by
  rw [woodinLocalOrderOn_eq_pullback hs]
  have h := (woodinIterationPrefix_of_stages hs).code
  exact forcingStageConditions_preorder h.system.split h.subset_universe h.system.order.preorder

theorem woodinStageMap_projection :
    IsForcingProjection
      (forcingDirectLimit θ (forcingCodeP (woodinIterationPrefix θ))
        (forcingCodeπ (woodinIterationPrefix θ)) (forcingCodeE (woodinIterationPrefix θ))
        (forcingCodeUniverse (woodinIterationPrefix θ)))
      (forcingThreadOrder θ (forcingCodeR (woodinIterationPrefix θ))
        (forcingDirectLimit θ (forcingCodeP (woodinIterationPrefix θ))
          (forcingCodeπ (woodinIterationPrefix θ)) (forcingCodeE (woodinIterationPrefix θ))
          (forcingCodeUniverse (woodinIterationPrefix θ))))
      (woodinStageCarrier θ) (woodinLocalOrderOn (woodinStageCarrier θ)) (woodinStageMap θ) := by
  rw [woodinLocalOrderOn_eq_pullback hs]
  have h := (woodinIterationPrefix_of_stages hs).code
  exact forcingStageThreadMap_projection h.system.split h.subset_universe

end ZFVP
