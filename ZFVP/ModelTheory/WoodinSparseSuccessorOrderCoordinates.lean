import ZFVP.ModelTheory.WoodinSparseCoordinateComparison
import ZFVP.ModelTheory.WoodinSparseBranchOrderComparison

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseStageCode_initial_order_coordinates {Ω p q : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
    (hp : p ∈ (forcingCodeP (woodinSparseStageCode (∅ : V))) ‘ ∅)
    (hq : q ∈ (forcingCodeP (woodinSparseStageCode (∅ : V))) ‘ ∅) :
    ⟨p, q⟩ₖ ∈ (forcingCodeR (woodinSparseStageCode (∅ : V))) ‘ ∅ ↔
      SparseOrderCoordinates ((forcingCodeP (woodinSparseStageCode (∅ : V))) ‘ ∅)
        ((forcingCodeR (woodinSparseStageCode (∅ : V))) ‘ ∅) (succ (woodinSourceIndex (∅ : V))) p q := by
  have hsub : (∅ : V) ⊆ Ω := empty_subset Ω
  have hc0 := woodinSparseStageCode_coordinate_empty hΩ hAC hsub hp
    (value_eq_empty_of_not_mem_domain (woodinSparseStageCode_no_zero hΩ hAC hsub hp))
    (value_eq_empty_of_not_mem_domain (woodinSparseStageCode_no_zero hΩ hAC hsub hq))
  have hc1 := woodinSparseStageCode_coordinate_comparison_iff (a := succ (∅ : V)) hΩ hAC hsub hp hq
  rw [woodinSparseStageCode_seed_cut hΩ hAC hsub, (woodinSparseStageCode_cut_seed_orders hΩ hAC hsub).1] at hc1
  have hp' := hp
  have hq' := hq
  rw [(woodinSparseStageCode_initial).1] at hp' hq'
  have hl := woodinSparseInitial_order_comparison hp' hq'
  rw [← (woodinSparseStageCode_initial).2] at hl
  have he := hl.trans hc1.symm
  rw [woodinSourceIndex_natural (show (∅ : V) ∈ (ω : V) by simp)]
  rw [sparseOrderCoordinates_successor, sparseOrderCoordinates_successor]
  have hz : SparseOrderCoordinates ((forcingCodeP (woodinSparseStageCode (∅ : V))) ‘ ∅)
      ((forcingCodeR (woodinSparseStageCode (∅ : V))) ‘ ∅) (∅ : V) p q := by
    intro b hb
    exact (not_mem_empty hb).elim
  simpa only [hz, hc0, true_and] using he

theorem woodinSparseStageCode_successor_order_coordinates {Ω k p q : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : succ k ⊆ Ω)
    (ih : ∀ p ∈ (forcingCodeP (woodinSparseStageCode k)) ‘ k,
      ∀ q ∈ (forcingCodeP (woodinSparseStageCode k)) ‘ k,
      ⟨p, q⟩ₖ ∈ (forcingCodeR (woodinSparseStageCode k)) ‘ k ↔
        SparseOrderCoordinates ((forcingCodeP (woodinSparseStageCode k)) ‘ k)
          ((forcingCodeR (woodinSparseStageCode k)) ‘ k) (succ (woodinSourceIndex k)) p q)
    (hp : p ∈ (forcingCodeP (woodinSparseStageCode (succ k))) ‘ (succ k))
    (hq : q ∈ (forcingCodeP (woodinSparseStageCode (succ k))) ‘ (succ k)) :
    ⟨p, q⟩ₖ ∈ (forcingCodeR (woodinSparseStageCode (succ k))) ‘ (succ k) ↔
      SparseOrderCoordinates ((forcingCodeP (woodinSparseStageCode (succ k))) ‘ (succ k))
        ((forcingCodeR (woodinSparseStageCode (succ k))) ‘ (succ k)) (succ (woodinSourceIndex (succ k))) p q := by
  have hi : k ∈ succ (succ k) := mem_succ_iff.mpr (Or.inr (mem_succ_self k))
  have hp' := woodinSparseStageCode_restrict_completed hΩ hAC hk hi hp
  have hq' := woodinSparseStageCode_restrict_completed hΩ hAC hk hi hq
  have hb := (ih _ hp' _ hq').trans (woodinSparseStageCode_coordinates_restriction hΩ hAC hk hi hp hq)
  have hc := woodinSparseStageCode_coordinate_comparison_iff (a := succ (woodinSourceIndex k)) hΩ hAC hk hp hq
  rw [← woodinSparseStageCode_carrier_recovery hΩ hAC hk hi,
    woodinSparseStageCode_cut_order_recovery hΩ hAC hk hi] at hc
  have hl := woodinSparseStageCode_successor_order_comparison hΩ hAC hk hp hq
  rw [(woodinSparsePrefixCode_row_at (mem_succ_self k)).1,
    (woodinSparsePrefixCode_row_at (mem_succ_self k)).2, woodinSourceIndex_successor] at hl
  rw [woodinSourceIndex_successor, sparseOrderCoordinates_successor]
  exact hl.trans (and_congr hb hc.symm)

end ZFVP
