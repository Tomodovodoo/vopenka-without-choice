import ZFVP.ModelTheory.WoodinSparseBaseRecovery
import ZFVP.SetTheory.ForcingRetractionFixedPoints

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def sparseCutOrder (S R a : V) : V :=
  forcingOrderRestriction (sparseCarrierCut S a) R

instance sparseCutOrder_definable : ℒₛₑₜ-function₃[V] sparseCutOrder := by
  unfold sparseCutOrder
  definability

theorem pair_mem_sparseCutOrder {S R a p q : V} :
    ⟨p, q⟩ₖ ∈ sparseCutOrder S R a ↔
      p ∈ sparseCarrierCut S a ∧ q ∈ sparseCarrierCut S a ∧ ⟨p, q⟩ₖ ∈ R :=
  pair_mem_forcingOrderRestriction _ _ _ _

theorem sparseCutOrder_preorder {S R a : V} (hR : IsForcingPreorder S R) :
    IsForcingPreorder (sparseCarrierCut S a) (sparseCutOrder S R a) :=
  forcingOrderRestriction_preorder hR (fun _ h ↦ (mem_sparseCarrierCut_iff.mp h).1)

theorem sparseCutOrder_top {S R a : V} (ht : IsForcingTop S R ∅) :
    IsForcingTop (sparseCarrierCut S a) (sparseCutOrder S R a) ∅ := by
  have h0 : (∅ : V) ∈ sparseCarrierCut S a := mem_sparseCarrierCut_iff.mpr ⟨ht.1, by simp⟩
  refine ⟨h0, fun p hp ↦ pair_mem_sparseCutOrder.mpr ⟨hp, h0, ?_⟩⟩
  exact ht.2 p (mem_sparseCarrierCut_iff.mp hp).1

theorem sparseCutOrder_eq_inter (S R a : V) :
    sparseCutOrder S R a = R ∩ (sparseCarrierCut S a ×ˢ sparseCarrierCut S a) := by
  apply mem_ext
  intro z
  simp only [sparseCutOrder, forcingOrderRestriction, mem_sep_iff, mem_inter_iff, and_comm]

theorem sparseCutOrder_idem {S R a b : V} (hab : a ⊆ b) :
    sparseCutOrder (sparseCarrierCut S b) (sparseCutOrder S R b) a = sparseCutOrder S R a := by
  rw [sparseCutOrder_eq_inter, sparseCarrierCut_idem hab, sparseCutOrder_eq_inter, sparseCutOrder_eq_inter]
  apply mem_ext
  intro z
  simp only [mem_inter_iff]
  constructor
  · exact fun h ↦ ⟨h.1.1, h.2⟩
  · rintro ⟨hzR, hz⟩
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hz
    have hp' := mem_sparseCarrierCut_iff.mp hp
    have hq' := mem_sparseCarrierCut_iff.mp hq
    exact ⟨⟨hzR, kpair_mem_iff.mpr
      ⟨mem_sparseCarrierCut_iff.mpr ⟨hp'.1, subset_trans hp'.2 hab⟩,
       mem_sparseCarrierCut_iff.mpr ⟨hq'.1, subset_trans hq'.2 hab⟩⟩⟩, hz⟩

theorem sparseFunction_domain_subset_carrier_rank {S a p : V} [IsOrdinal a]
    (hsp : ∀ p ∈ S, IsSparseFunctionOn a p) (hp : p ∈ S) : domain p ⊆ rank S := by
  have hs := hsp p hp
  let := hs.1
  let := hierarchy_transitive (rank S)
  intro x hx
  let := IsOrdinal.of_mem (hs.2.1 x hx)
  have hv := (kpair_components_mem_transitive
    ((hierarchy_transitive (rank S)).mem_trans (kpair_value_mem hx) (subset_hierarchy_rank S p hp))).1
  exact ordinal_mem_hierarchy_iff.mp hv

theorem sparseCarrierCut_succ_rank {S a : V} [IsOrdinal a]
    (hsp : ∀ p ∈ S, IsSparseFunctionOn a p) : sparseCarrierCut S (succ (rank S)) = S := by
  apply mem_ext
  intro p
  rw [mem_sparseCarrierCut_iff]
  exact ⟨fun h ↦ h.1, fun hp ↦ ⟨hp,
    subset_trans (sparseFunction_domain_subset_carrier_rank hsp hp) (mem_subset_refl _)⟩⟩

theorem sparseCutOrder_succ_rank {S R a : V} [IsOrdinal a]
    (hR : IsForcingPreorder S R) (hsp : ∀ p ∈ S, IsSparseFunctionOn a p) :
    sparseCutOrder S R (succ (rank S)) = R := by
  rw [sparseCutOrder_eq_inter, sparseCarrierCut_succ_rank hsp]
  apply mem_ext
  intro z
  rw [mem_inter_iff]
  exact ⟨fun h ↦ h.1, fun hz ↦ ⟨hz, hR.1 z hz⟩⟩

end ZFVP
