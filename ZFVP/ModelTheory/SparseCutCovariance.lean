import ZFVP.ModelTheory.WoodinSparseOrderCovariance
import ZFVP.SetTheory.NameHierarchyTableFormula

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedOrderRestrictionFormula : SetTheorySemisentence 3 :=
  “K C R. !isSubsetOf K R ∧ !boundedSubsetProductFormula K C C ∧
    ∀ p ∈ C, ∀ q ∈ C, !boundedPairMemberFormula R p q → !boundedPairMemberFormula K p q”

theorem boundedOrderRestrictionFormula_bounded : IsBoundedSetFormula boundedOrderRestrictionFormula := by
  repeat' first
    | exact isSubsetOf_bounded.subst _
    | exact boundedSubsetProductFormula_bounded.subst _
    | exact boundedPairMemberFormula_bounded.subst _
    | exact (boundedPairMemberFormula_bounded.subst _).neg
    | apply IsBoundedSetFormula.all
    | apply IsBoundedSetFormula.and
    | apply IsBoundedSetFormula.or

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedOrderRestrictionFormula_defined :
    ℒₛₑₜ-function₂[V] forcingOrderRestriction via boundedOrderRestrictionFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [boundedOrderRestrictionFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def,
    eval_boundedSubsetProductFormula]
  constructor
  · rintro ⟨hs, hp, h⟩
    apply mem_ext
    intro z
    change z ∈ v 0 ↔ z ∈ sep (v 1 ×ˢ v 1) (fun z ↦ z ∈ v 2) _
    rw [mem_sep_iff]
    constructor
    · exact fun hz ↦ ⟨hp z hz, hs z hz⟩
    · rintro ⟨hz, hr⟩
      obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hz
      exact h p hp q hq hr
  · intro he
    rw [he]
    refine ⟨?_, ?_, ?_⟩
    · exact fun _ hz ↦ (mem_sep_iff.mp hz).2
    · exact fun _ hz ↦ (mem_sep_iff.mp hz).1
    · intro p hp q hq hr
      exact mem_sep_iff.mpr ⟨kpair_mem_iff.mpr ⟨hp, hq⟩, hr⟩

theorem IsCodedMembershipEmbedding.value_sparseCarrierCut {A B f S a : V}
    [IsTransitive A] [IsTransitive B] (he : IsCodedMembershipEmbedding A B f)
    (hS : S ∈ A) (ha : a ∈ A) (hcut : sparseCarrierCut S a ∈ A) :
    f ‘ (sparseCarrierCut S a) = sparseCarrierCut (f ‘ S) (f ‘ a) :=
  (he.bounded_defined_iff boundedSparseCarrierCutFormula_bounded
    (fun v ↦ v 0 = sparseCarrierCut (v 1) (v 2)) ![sparseCarrierCut S a, S, a]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hcut, hS, ha])).mp rfl

theorem IsCodedMembershipEmbedding.value_orderRestriction {A B f C R : V}
    [IsTransitive A] [IsTransitive B] (he : IsCodedMembershipEmbedding A B f)
    (hC : C ∈ A) (hR : R ∈ A) (hcut : forcingOrderRestriction C R ∈ A) :
    f ‘ (forcingOrderRestriction C R) = forcingOrderRestriction (f ‘ C) (f ‘ R) :=
  (he.bounded_defined_iff boundedOrderRestrictionFormula_bounded
    (fun v ↦ v 0 = forcingOrderRestriction (v 1) (v 2)) ![forcingOrderRestriction C R, C, R]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hcut, hC, hR])).mp rfl

theorem IsCodedMembershipEmbedding.value_sparseCutOrder {A B f S R a : V}
    [IsTransitive A] [IsTransitive B] (he : IsCodedMembershipEmbedding A B f)
    (hS : S ∈ A) (hR : R ∈ A) (ha : a ∈ A)
    (hC : sparseCarrierCut S a ∈ A) (hK : sparseCutOrder S R a ∈ A) :
    f ‘ (sparseCutOrder S R a) = sparseCutOrder (f ‘ S) (f ‘ R) (f ‘ a) := by
  unfold sparseCutOrder at hK ⊢
  rw [he.value_orderRestriction hC hR hK, he.value_sparseCarrierCut hS ha hC]

theorem limitRankEmbedding_sparse_cuts {δ ε f S R a : V} [IsOrdinal δ] [IsOrdinal ε]
    (hδ : ∀ β ∈ δ, succ β ∈ δ)
    (he : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hS : S ∈ hierarchy δ) (hR : R ∈ hierarchy δ) (ha : a ∈ hierarchy δ) :
    f ‘ (sparseCarrierCut S a) = sparseCarrierCut (f ‘ S) (f ‘ a) ∧
      f ‘ (sparseCutOrder S R a) = sparseCutOrder (f ‘ S) (f ‘ R) (f ‘ a) := by
  let := hierarchy_transitive δ
  let := hierarchy_transitive ε
  have hC : sparseCarrierCut S a ∈ hierarchy δ := subset_mem_hierarchy_limit hδ hS
    (fun _ hp ↦ (mem_sparseCarrierCut_iff.mp hp).1)
  have hK : sparseCutOrder S R a ∈ hierarchy δ := subset_mem_hierarchy_limit hδ hR (by
    rw [sparseCutOrder_eq_inter]
    exact fun _ hz ↦ (mem_inter_iff.mp hz).1)
  exact ⟨he.value_sparseCarrierCut hS ha hC, he.value_sparseCutOrder hS hR ha hC hK⟩

variable {Ω Ξ θ ξ f a : V} [IsOrdinal θ] [IsOrdinal ξ]
local notation "P" => (forcingCodeP (woodinSparseStageCode θ)) ‘ θ
local notation "R" => (forcingCodeR (woodinSparseStageCode θ)) ‘ θ
local notation "Q" => (forcingCodeP (woodinSparseStageCode ξ)) ‘ ξ
local notation "D" => (forcingCodeR (woodinSparseStageCode ξ)) ‘ ξ
local notation "η" => rank P
local notation "ζ" => rank Q

theorem woodinSparseStageCode_cut_covariance
    (hΩ : IsWoodinSupercompact Ω) (hΞ : IsWoodinSupercompact Ξ)
    (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hξ : ξ ⊆ Ξ)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd η (ω : V)))
      (hierarchy (ordinalAdd ζ (ω : V))) f) (hP : f ‘ P = Q)
    (ha : a ∈ hierarchy (ordinalAdd η (ω : V))) :
    f ‘ (sparseCarrierCut P a) = sparseCarrierCut Q (f ‘ a) ∧
      f ‘ (sparseCutOrder P R a) = sparseCutOrder Q D (f ‘ a) := by
  have hδ : ∀ β ∈ ordinalAdd η (ω : V), succ β ∈ ordinalAdd η (ω : V) :=
    fun _ hb ↦ ordinalAdd_omega_succ_closed η hb
  have hpA : P ∈ hierarchy (ordinalAdd η (ω : V)) :=
    (mem_hierarchy_iff_rank_mem _ _).mpr (ordinalAdd_omega_gt η)
  have hrA : R ∈ hierarchy (ordinalAdd η (ω : V)) := by
    apply mem_hierarchy_of_mem_stage (hδ _ (ordinalAdd_omega_gt η))
    rw [← woodinSparseStageCode_order_from_carrier hΩ hAC hθ]
    exact sparseCarrierOrder_mem_successor
      (woodinSparseStageCode_rank_inaccessible hΩ hAC hθ).rankCriterion.2.2.1 (subset_hierarchy_rank P)
  have hh := limitRankEmbedding_sparse_cuts hδ he hpA hrA ha
  rw [hP, woodinSparseStageCode_order_covariance hΩ hΞ hAC hθ hξ he hP] at hh
  exact hh

end ZFVP
