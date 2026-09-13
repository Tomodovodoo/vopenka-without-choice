import ZFVP.ModelTheory.WoodinSparseOrderCoordinates
import ZFVP.ModelTheory.WoodinSparseCutCoordinates
import ZFVP.ModelTheory.SparseOrderIdentification
import ZFVP.ModelTheory.WoodinSparseExactRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]
local notation "P" => (forcingCodeP (woodinSparseStageCode θ)) ‘ θ
local notation "R" => (forcingCodeR (woodinSparseStageCode θ)) ‘ θ

theorem woodinSparseStageCode_carrier_only_cut_order
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (a : V) [IsOrdinal a] : sparseCarrierOrder P a = sparseCutOrder P R a := by
  apply sparseCarrierOrder_eq_cut_of_coordinates
  intro b hb p hp q hq
  let := hb
  exact (woodinSparseStageCode_order_coordinates hΩ hAC hθ
    (mem_sparseCarrierCut_iff.mp hp).1 (mem_sparseCarrierCut_iff.mp hq).1).trans
    (woodinSparseStageCode_coordinates_cut_iff hΩ hAC hθ hp hq)

theorem woodinSparseStageCode_carrier_only_order
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    sparseCarrierOrder P (succ (woodinSourceIndex θ)) = R := by
  rw [woodinSparseStageCode_carrier_only_cut_order hΩ hAC hθ,
    woodinSparseStageCode_cut_order_recovery hΩ hAC hθ (mem_succ_self θ)]

theorem woodinSparseStageCode_order_from_carrier
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    sparseRecoveredOrder P = R := by
  unfold sparseRecoveredOrder
  rw [woodinSparseStageCode_carrier_only_cut_order hΩ hAC hθ]
  exact sparseCutOrder_succ_rank
    ((woodinSparseStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ))
    (fun _ hp ↦ woodinSparseStageCode_sparse hΩ hAC hθ hp)

theorem woodinSparseSourceStageCode_carrier_only_order
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ succ (woodinSourceIndex θ)) :
    sparseCarrierOrder ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)) (succ i) =
      (forcingCodeR (woodinSparseSourceStageCode θ)) ‘ i := by
  rw [(woodinSparseSourceStageCode_row (mem_succ_self θ)).1]
  have hi' : i ∈ woodinSourceIndex (succ θ) := by simpa only [woodinSourceIndex_successor] using hi
  rcases woodinSourceIndex_cases hi' with he | ⟨j, hj, he⟩
  · subst i
    rw [(woodinSparseSourceStageCode_seed (θ := θ)).2.1,
      woodinSparseStageCode_carrier_only_cut_order hΩ hAC hθ,
      (woodinSparseStageCode_cut_seed_orders hΩ hAC hθ).1]
  · subst i
    let := IsOrdinal.of_mem hj
    rw [(woodinSparseSourceStageCode_row hj).2, (woodinSparseStage_old_row hj).2,
      woodinSparseStageCode_carrier_only_cut_order hΩ hAC hθ,
      woodinSparseStageCode_cut_order_recovery hΩ hAC hθ hj]

theorem woodinSparseStageCode_endpoint_order_from_carrier
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    sparseCarrierOrder ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω)
      (succ (rank ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω))) =
      (forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω := by
  let := hΩ.inaccessible.1
  rw [woodinSparseStageCode_rank_eq hΩ hAC (subset_refl Ω), woodinIteration_endpoint_cardinal hΩ hAC]
  have he : woodinSourceIndex Ω = Ω := woodinSourceIndex_infinite
    (fun h ↦ mem_asymm h hΩ.inaccessible.2.1)
  simpa only [he] using woodinSparseStageCode_carrier_only_order hΩ hAC (subset_refl Ω)

end ZFVP
