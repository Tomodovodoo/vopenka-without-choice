import ZFVP.ModelTheory.WoodinSparseCarrierOnlyOrder
import ZFVP.ModelTheory.SparseOrderCertificateExistence

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem function_value_mem_transitive {T p : V} [IsTransitive T] [IsFunction p]
    (h0 : (∅ : V) ∈ T) (hp : p ∈ T) (b : V) : p ‘ b ∈ T := by
  classical
  by_cases hb : b ∈ domain p
  · obtain ⟨y, hy⟩ := mem_domain_iff.mp hb
    rw [value_eq_of_kpair_mem hy]
    exact (subname_pair_components_mem_transitive hp hy).2
  · rw [value_eq_empty_of_not_mem_domain hb]
    exact h0

theorem function_restrict_mem_hierarchy_limit {η p : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hp : p ∈ hierarchy η) (b : V) : p ↾ b ∈ hierarchy η :=
  subset_mem_hierarchy_limit hη hp (fun _ hz ↦ (mem_restrict_iff.mp hz).1)

variable {Ω θ : V} [IsOrdinal θ]
local notation "P" => (forcingCodeP (woodinSparseStageCode θ)) ‘ θ
local notation "R" => (forcingCodeR (woodinSparseStageCode θ)) ‘ θ

theorem woodinSparseStageCode_candidate_preorder
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (b : V) [IsOrdinal b] : IsForcingPreorder (sparseCarrierCut P b) (sparseCarrierOrder P b) := by
  rw [woodinSparseStageCode_carrier_only_cut_order hΩ hAC hθ]
  exact sparseCutOrder_preorder
    ((woodinSparseStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ))

theorem woodinSparseStageCode_certificate_support {η : V} [IsOrdinal η]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hη : ∀ β ∈ η, succ β ∈ η) (h0 : (∅ : V) ∈ hierarchy η) (hP : P ⊆ hierarchy η)
    {p : V} (hp : p ∈ P) (b : V) : p ↾ b ∈ hierarchy η ∧ p ‘ b ∈ hierarchy η := by
  let := (woodinSparseStageCode_sparse hΩ hAC hθ hp).1
  let := hierarchy_transitive η
  exact ⟨function_restrict_mem_hierarchy_limit hη (hP p hp) b,
    function_value_mem_transitive h0 (hP p hp) b⟩

theorem woodinSparseStageCode_order_certificate_unique {W T a C O E : V}
    [IsOrdinal a] [IsTransitive T]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hc : boundedSparseOrderCertificateFormula.Evalb ![W, T, P, a, C, O, E])
    (hsupp : ∀ b ∈ a, ∀ p ∈ P, p ↾ b ∈ T ∧ p ‘ b ∈ T) :
    ∀ b ∈ a, O ‘ b = sparseCutOrder P R b := by
  have hh := sparseOrderCertificate_unique hc (by
    intro b hb
    let := IsOrdinal.of_mem hb
    exact woodinSparseStageCode_candidate_preorder hΩ hAC hθ b) (by
    intro b hb p hp
    let := IsOrdinal.of_mem hb
    exact woodinSparseStageCode_coordinate_isName hΩ hAC hθ hp) hsupp
  intro b hb
  let := IsOrdinal.of_mem hb
  exact (hh b hb).trans (woodinSparseStageCode_carrier_only_cut_order hΩ hAC hθ b)

end ZFVP
