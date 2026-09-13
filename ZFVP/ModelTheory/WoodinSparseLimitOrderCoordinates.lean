import ZFVP.ModelTheory.SparseOrderCoordinates
import ZFVP.ModelTheory.WoodinSparseCutDictionary
import ZFVP.ModelTheory.WoodinSparseCoordinateNames
import ZFVP.ModelTheory.WoodinSparseBranchOrderComparison
import ZFVP.ModelTheory.WoodinSparseCoordinateComparison

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ p q : V} [IsOrdinal θ]

local notation:max "P" i:max => (forcingCodeP (woodinSparseStageCode i)) ‘ i
local notation:max "R" i:max => (forcingCodeR (woodinSparseStageCode i)) ‘ i

theorem woodinSparseStageCode_limit_prefix_coordinates
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (ih : ∀ i ∈ θ, ∀ p ∈ P i, ∀ q ∈ P i,
      ⟨p, q⟩ₖ ∈ R i ↔ SparseOrderCoordinates (P i) (R i) (succ (woodinSourceIndex i)) p q)
    (hp : p ∈ P θ) (hq : q ∈ P θ) :
    (∀ i ∈ θ, ⟨p ↾ (succ (woodinSourceIndex i)), q ↾ (succ (woodinSourceIndex i))⟩ₖ ∈ R i) ↔
      SparseOrderCoordinates (P θ) (R θ) θ p q := by
  let := (woodinSparseStageCode_sparse hΩ hAC hθ hp).1
  let := (woodinSparseStageCode_sparse hΩ hAC hθ hq).1
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hl := ordinal_limit_of_not_successor hlim
  have he (i : V) (hi : i ∈ θ) :
      (⟨p ↾ (succ (woodinSourceIndex i)), q ↾ (succ (woodinSourceIndex i))⟩ₖ ∈ R i) ↔
        SparseOrderCoordinates (P θ) (R θ) (succ (woodinSourceIndex i)) p q := by
    let := IsOrdinal.of_mem hi
    have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
    rw [ih i hi _ (woodinSparseStageCode_restrict_mem hΩ hAC hθ hi hp)
      _ (woodinSparseStageCode_restrict_mem hΩ hAC hθ hi hq)]
    exact woodinSparseStageCode_coordinates_restriction hΩ hAC hθ hi' hp hq
  constructor
  · intro h b hb
    obtain ⟨i, hi, hb⟩ := woodinSparseBounds_cover hb
    rw [woodinSparseBounds_value hi] at hb
    exact (he i hi).mp (h i hi) b hb
  · intro h i hi
    apply (he i hi).mpr
    intro b hb
    have hc := woodinSparseBounds_limit_subset hz hl hi
    rw [woodinSparseBounds_value hi] at hc
    exact h b (hc b hb)

theorem woodinSparseStageCode_direct_order_coordinates
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (ih : ∀ i ∈ θ, ∀ p ∈ P i, ∀ q ∈ P i,
      ⟨p, q⟩ₖ ∈ R i ↔ SparseOrderCoordinates (P i) (R i) (succ (woodinSourceIndex i)) p q)
    (hp : p ∈ P θ) (hq : q ∈ P θ) :
    ⟨p, q⟩ₖ ∈ R θ ↔ SparseOrderCoordinates (P θ) (R θ) (succ (woodinSourceIndex θ)) p q := by
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hR := (woodinSparseStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ)
  have ht := (woodinSparseStageCode_valid hΩ hAC hθ).system.tops.top θ (mem_succ_self θ)
  rw [woodinSparseStageCode_top hΩ hAC hθ] at ht
  have hlast : SparseCoordinateComparison (P θ) (R θ) θ p q := by
    apply sparseCoordinateComparison_empty hR ht
    · exact woodinSparseStageCode_restrict_mem_cut hΩ hAC hθ hp
    · exact value_eq_empty_of_not_mem_domain (woodinSparseStageCode_direct_no_self hΩ hAC hθ h0 hlim hn hp)
    · exact value_eq_empty_of_not_mem_domain (woodinSparseStageCode_direct_no_self hΩ hAC hθ h0 hlim hn hq)
  rw [woodinSourceIndex_limit θ hz (ordinal_limit_of_not_successor hlim),
    sparseOrderCoordinates_successor, and_iff_left hlast,
    ← woodinSparseStageCode_limit_prefix_coordinates hΩ hAC hθ h0 hlim ih hp hq]
  have hp' := hp
  have hq' := hq
  rw [(woodinSparseStageCode_direct h0 hlim hn).1] at hp' hq'
  rw [(woodinSparseStageCode_direct h0 hlim hn).2, woodinSparseDirectOrder, mem_sparseThreadOrder_iff]
  simp only [hp', hq', true_and]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  rw [woodinSparseBounds_value hi, (woodinSparsePrefixCode_row_at hi).2]

theorem woodinSparseStageCode_inverse_order_coordinates
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (ih : ∀ i ∈ θ, ∀ p ∈ P i, ∀ q ∈ P i,
      ⟨p, q⟩ₖ ∈ R i ↔ SparseOrderCoordinates (P i) (R i) (succ (woodinSourceIndex i)) p q)
    (hp : p ∈ P θ) (hq : q ∈ P θ) :
    ⟨p, q⟩ₖ ∈ R θ ↔ SparseOrderCoordinates (P θ) (R θ) (succ (woodinSourceIndex θ)) p q := by
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hl := ordinal_limit_of_not_successor hlim
  have hp' := hp
  have hq' := hq
  rw [(woodinSparseStageCode_inverse h0 hlim hn).1] at hp' hq'
  have hpb := (mem_sparsePairCarrier_iff.mp hp').2.1
  have hqb := (mem_sparsePairCarrier_iff.mp hq').2.1
  have hbase : ⟨p ↾ θ, q ↾ θ⟩ₖ ∈ woodinSparseInverseOrder θ (woodinSparsePrefixCode θ) ↔
      SparseOrderCoordinates (P θ) (R θ) θ p q := by
    rw [← woodinSparseStageCode_limit_prefix_coordinates hΩ hAC hθ h0 hlim ih hp hq]
    rw [woodinSparseInverseOrder, mem_sparseThreadOrder_iff]
    simp only [hpb, hqb, true_and]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    have hc := woodinSparseBounds_limit_subset hz hl hi
    rw [woodinSparseBounds_value hi] at hc
    rw [woodinSparseBounds_value hi, (woodinSparsePrefixCode_row_at hi).2,
      restrict_restrict_of_subset hc, restrict_restrict_of_subset hc]
  rw [woodinSourceIndex_limit θ hz hl, sparseOrderCoordinates_successor,
    woodinSparseStageCode_inverse_order_comparison hΩ hAC hθ h0 hlim hn hp hq, hbase]
  apply and_congr_right
  intro _
  rw [woodinSparseStageCode_coordinate_comparison_iff hΩ hAC hθ hp hq,
    woodinSparseStageCode_raw_inverse_recovery hΩ hAC hθ h0 hlim hn,
    woodinSparseStageCode_cut_inverse_order hΩ hAC hθ (mem_succ_self θ) h0 hlim hn]

end ZFVP
