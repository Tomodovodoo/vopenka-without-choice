import ZFVP.ModelTheory.WoodinSparseLocalPrefixRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω : V} [IsOrdinal Ω]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
local notation "P" => (forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω
local notation "R" => (forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω
include hΩ hAC

theorem woodinSparse_prefix_carrier_subset {i : V} (hi : i ∈ Ω) :
    ((forcingCodeP (woodinSparseStageCode i)) ‘ i) ⊆ P := by
  have hi' : i ∈ succ Ω := mem_succ_iff.mpr (Or.inr hi)
  have hv := woodinSparseStageCode_valid hΩ hAC (subset_refl Ω)
  have hπ := hv.system.splitProjection hi' (mem_succ_self Ω)
    (IsOrdinal.toIsTransitive.transitive _ hi)
  have he := hπ.subset_of_section_identity
    (fun p hp ↦ woodinSparseStageCode_section hΩ hAC (subset_refl Ω) hi hp)
  rwa [(woodinSparseStage_old_row hi').1] at he

theorem woodinSparse_prefix_order_iff {i p q : V} (hi : i ∈ Ω)
    (hp : p ∈ (forcingCodeP (woodinSparseStageCode i)) ‘ i)
    (hq : q ∈ (forcingCodeP (woodinSparseStageCode i)) ‘ i) :
    ⟨p, q⟩ₖ ∈ (forcingCodeR (woodinSparseStageCode i)) ‘ i ↔ ⟨p, q⟩ₖ ∈ R := by
  have hi' : i ∈ succ Ω := mem_succ_iff.mpr (Or.inr hi)
  have hv := woodinSparseStageCode_valid hΩ hAC (subset_refl Ω)
  have hπ := hv.system.splitProjection hi' (mem_succ_self Ω)
    (IsOrdinal.toIsTransitive.transitive _ hi)
  have hp' := hp
  have hq' := hq
  rw [← (woodinSparseStage_old_row hi').1] at hp' hq'
  have hEp := woodinSparseStageCode_section hΩ hAC (subset_refl Ω) hi hp'
  have hEq := woodinSparseStageCode_section hΩ hAC (subset_refl Ω) hi hq'
  have hback := hπ.right_inverse p hp'
  rw [hEp] at hback
  have he := hπ.below p (woodinSparse_prefix_carrier_subset hΩ hAC hi p hp) q hq'
  rw [hEq, hback, (woodinSparseStage_old_row hi').2] at he
  exact he.symm

theorem woodinSparse_endpoint_carrier_union (p : V) :
    p ∈ P ↔ ∃ i ∈ Ω, p ∈ (forcingCodeP (woodinSparseStageCode i)) ‘ i := by
  constructor
  · intro hp
    have hpΩ := woodinSparseStageCode_rows_subset_at_endpoint hΩ hAC Ω (mem_succ_self Ω) p hp
    have hr := (mem_hierarchy_iff_rank_mem p Ω).mp hpΩ
    have hi := hΩ.inaccessible.rankCriterion.2.2.1 (rank p) hr
    refine ⟨succ (rank p), hi, ?_⟩
    exact woodinSparse_condition_mem_prefix_of_rank hΩ hAC (subset_refl Ω)
      (mem_succ_iff.mpr (Or.inr hi)) hp
      ((mem_hierarchy_iff_rank_mem p (succ (rank p))).mpr (mem_succ_self (rank p)))
  · rintro ⟨i, hi, hp⟩
    exact woodinSparse_prefix_carrier_subset hΩ hAC hi p hp

theorem woodinSparse_endpoint_order_union (p q : V) :
    ⟨p, q⟩ₖ ∈ R ↔ ∃ i ∈ Ω, ⟨p, q⟩ₖ ∈ (forcingCodeR (woodinSparseStageCode i)) ‘ i := by
  have hv := woodinSparseStageCode_valid hΩ hAC (subset_refl Ω)
  have hR := hv.system.order.preorder Ω (mem_succ_self Ω)
  constructor
  · intro hpq
    have hpp : p ∈ P ∧ q ∈ P := by simpa using hR.1 _ hpq
    obtain ⟨hp, hq⟩ := hpp
    have hpΩ := woodinSparseStageCode_rows_subset_at_endpoint hΩ hAC Ω (mem_succ_self Ω) p hp
    have hqΩ := woodinSparseStageCode_rows_subset_at_endpoint hΩ hAC Ω (mem_succ_self Ω) q hq
    obtain ⟨i, hi, hpi, hqi⟩ := common_hierarchy_stage hΩ.inaccessible.rankCriterion.2.2.1 hpΩ hqΩ
    let := IsOrdinal.of_mem hi
    have hi' : i ∈ succ Ω := mem_succ_iff.mpr (Or.inr hi)
    have hpp := woodinSparse_condition_mem_prefix_of_rank hΩ hAC (subset_refl Ω) hi' hp hpi
    have hqq := woodinSparse_condition_mem_prefix_of_rank hΩ hAC (subset_refl Ω) hi' hq hqi
    exact ⟨i, hi, (woodinSparse_prefix_order_iff hΩ hAC hi hpp hqq).mpr hpq⟩
  · rintro ⟨i, hi, hpq⟩
    have hi' : i ∈ succ Ω := mem_succ_iff.mpr (Or.inr hi)
    have hRi := hv.system.order.preorder i hi'
    rw [(woodinSparseStage_old_row hi').1, (woodinSparseStage_old_row hi').2] at hRi
    have hpp : p ∈ (forcingCodeP (woodinSparseStageCode i)) ‘ i ∧ q ∈ (forcingCodeP (woodinSparseStageCode i)) ‘ i := by simpa using hRi.1 _ hpq
    obtain ⟨hp, hq⟩ := hpp
    exact (woodinSparse_prefix_order_iff hΩ hAC hi hp hq).mp hpq

end ZFVP

