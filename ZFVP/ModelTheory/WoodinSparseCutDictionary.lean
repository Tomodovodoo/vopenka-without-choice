import ZFVP.ModelTheory.SparseCutOrder
import ZFVP.ModelTheory.WoodinSparseOrderRecovery
import ZFVP.ModelTheory.WoodinSparseInverseOrderRecovery
import ZFVP.ModelTheory.WoodinSparseSourceCarrierRecovery

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem sparseCarrierCut_singleton_empty (a : V) : sparseCarrierCut ({∅} : V) a = {∅} := by
  apply mem_ext
  intro p
  simp only [mem_sparseCarrierCut_iff, mem_singleton_iff]
  exact ⟨fun h ↦ h.1, fun he ↦ ⟨he, by simp [he]⟩⟩

theorem sparseCutOrder_singleton {S R a : V} (ht : IsForcingTop S R ∅)
    (ha : sparseCarrierCut S a = {∅}) : sparseCutOrder S R a = ({∅} : V) ×ˢ {∅} := by
  rw [sparseCutOrder_eq_inter, ha]
  apply mem_ext
  intro z
  rw [mem_inter_iff]
  constructor
  · exact fun h ↦ h.2
  · intro hz
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hz
    have hp0 := mem_singleton_iff.mp hp
    have hq0 := mem_singleton_iff.mp hq
    subst p
    subst q
    exact ⟨ht.2 ∅ ht.1, hz⟩

variable {Ω θ : V} [IsOrdinal θ]

theorem woodinSparsePrefixCode_row_at {i : V} (hi : i ∈ θ) :
    (forcingCodeP (woodinSparsePrefixCode θ)) ‘ i = (forcingCodeP (woodinSparseStageCode i)) ‘ i ∧
    (forcingCodeR (woodinSparsePrefixCode θ)) ‘ i = (forcingCodeR (woodinSparseStageCode i)) ‘ i := by
  rw [(woodinSparseStageCode_row i).1, (woodinSparseStageCode_row i).2]
  simp only [woodinSparsePrefixCode, forcingRecodedCode, forcingCodeP_code, forcingCodeR_code,
    (woodinSparseRecodingHistory_values hi).1, (woodinSparseRecodingHistory_values hi).2.1, and_self]

theorem woodinSparseStageCode_cut_order_recovery
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ succ θ) :
    sparseCutOrder ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
      ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) (succ (woodinSourceIndex i)) =
      (forcingCodeR (woodinSparseStageCode i)) ‘ i := by
  rw [sparseCutOrder_eq_inter]
  exact (woodinSparseStageCode_order_recovery hΩ hAC hθ hi).symm

theorem woodinSparseStageCode_cut_zero
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    sparseCarrierCut ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) (∅ : V) = {∅} := by
  rw [← sparseCarrierCut_idem (a := (∅ : V)) (b := succ ∅) (empty_subset _),
    woodinSparseStageCode_seed_cut hΩ hAC hθ, sparseCarrierCut_singleton_empty]

theorem woodinSparseStageCode_cut_seed_orders
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    sparseCutOrder ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
      ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) (succ (∅ : V)) = ({∅} : V) ×ˢ {∅} ∧
    sparseCutOrder ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
      ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) (∅ : V) = ({∅} : V) ×ˢ {∅} := by
  have ht := (woodinSparseStageCode_valid hΩ hAC hθ).system.tops.top θ (mem_succ_self θ)
  rw [woodinSparseStageCode_top hΩ hAC hθ] at ht
  exact ⟨sparseCutOrder_singleton ht (woodinSparseStageCode_seed_cut hΩ hAC hθ),
    sparseCutOrder_singleton ht (woodinSparseStageCode_cut_zero hΩ hAC hθ)⟩

theorem woodinSparseStageCode_cut_inverse_order {i : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hi : i ∈ succ θ) (h0 : i ≠ ∅) (hlim : i ≠ succ (⋃ˢ i))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix i))) :
    sparseCutOrder ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
      ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) i =
      woodinSparseInverseOrder i (woodinSparsePrefixCode i) := by
  rw [sparseCutOrder_eq_inter]
  exact (woodinSparseStageCode_earlier_raw_inverse_order_recovery hΩ hAC hθ hi h0 hlim hn).symm

end ZFVP
