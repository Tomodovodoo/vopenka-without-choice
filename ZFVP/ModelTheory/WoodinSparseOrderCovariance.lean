import ZFVP.ModelTheory.WoodinSparseFiniteOrderCertificate
import ZFVP.ModelTheory.LimitRankEmbeddingAction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω Ξ θ ξ f : V} [IsOrdinal θ] [IsOrdinal ξ]
local notation "P" => (forcingCodeP (woodinSparseStageCode θ)) ‘ θ
local notation "R" => (forcingCodeR (woodinSparseStageCode θ)) ‘ θ
local notation "Q" => (forcingCodeP (woodinSparseStageCode ξ)) ‘ ξ
local notation "D" => (forcingCodeR (woodinSparseStageCode ξ)) ‘ ξ
local notation "η" => rank P
local notation "ζ" => rank Q
local notation "A" => hierarchy (ordinalAdd η (ω : V))
local notation "B" => hierarchy (ordinalAdd ζ (ω : V))

theorem woodinSparseStageCode_order_covariance
    (hΩ : IsWoodinSupercompact Ω) (hΞ : IsWoodinSupercompact Ξ)
    (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hξ : ξ ⊆ Ξ)
    (he : IsCodedMembershipEmbedding A B f) (hP : f ‘ P = Q) : f ‘ R = D := by
  let := hierarchy_transitive (ordinalAdd η (ω : V))
  let := hierarchy_transitive (ordinalAdd ζ (ω : V))
  have hη := woodinSparseStageCode_rank_inaccessible hΩ hAC hθ
  have hζ := woodinSparseStageCode_rank_inaccessible hΞ hAC hξ
  have hδ : ∀ β ∈ ordinalAdd η (ω : V), succ β ∈ ordinalAdd η (ω : V) :=
    fun _ hb ↦ ordinalAdd_omega_succ_closed η hb
  have hε : ∀ β ∈ ordinalAdd ζ (ω : V), succ β ∈ ordinalAdd ζ (ω : V) :=
    fun _ hb ↦ ordinalAdd_omega_succ_closed ζ hb
  have hηδ := ordinalAdd_omega_gt η
  have h1 := hδ _ hηδ
  have h2 := hδ _ h1
  have hpA : P ∈ A := (mem_hierarchy_iff_rank_mem _ _).mpr hηδ
  have hrA : R ∈ A := by
    apply mem_hierarchy_of_mem_stage h1
    rw [← woodinSparseStageCode_order_from_carrier hΩ hAC hθ]
    exact sparseCarrierOrder_mem_successor hη.rankCriterion.2.2.1 (subset_hierarchy_rank P)
  have hηA : η ∈ A := ordinal_subset_hierarchy _ _ hηδ
  have h1A : succ η ∈ A := ordinal_subset_hierarchy _ _ h1
  have h2A : succ (succ η) ∈ A := ordinal_subset_hierarchy _ _ h2
  have htA : hierarchy η ∈ A := hierarchy_mem hηδ
  have hwA : hierarchy (succ η) ∈ A := hierarchy_mem h1
  have hfη : f ‘ η = ζ := by
    rw [limitRankEmbedding_value_rank hδ he hpA, hP]
  have hf1 : f ‘ (succ η) = succ ζ := by rw [he.value_succ hηA h1A, hfη]
  have hf2 : f ‘ (succ (succ η)) = succ (succ ζ) := by rw [he.value_succ h1A h2A, hf1]
  have hft : f ‘ (hierarchy η) = hierarchy ζ := by
    rw [(limitRankEmbedding_value_hierarchy hδ hε he inferInstance hηA).2, hfη]
  have hfw : f ‘ (hierarchy (succ η)) = hierarchy (succ ζ) := by
    rw [(limitRankEmbedding_value_hierarchy hδ hε he inferInstance h1A).2, hf1]
  obtain ⟨C, hC, O, hO, E, hE, hc, hv⟩ := woodinSparseStageCode_finite_order_certificate hΩ hAC hθ
  have hparams : ∀ i, (![hierarchy (succ η), hierarchy η, P, succ (succ η), C, O, E] i) ∈ A := by
    intro i
    fin_cases i <;> assumption
  have hc' := (he.bounded_formula_iff boundedSparseOrderCertificateFormula_bounded
    ![hierarchy (succ η), hierarchy η, P, succ (succ η), C, O, E] hparams).mp hc
  have hvec : (fun i ↦ f ‘ (![hierarchy (succ η), hierarchy η, P, succ (succ η), C, O, E] i)) =
      ![hierarchy (succ ζ), hierarchy ζ, Q, succ (succ ζ), f ‘ C, f ‘ O, f ‘ E] := by
    funext i
    fin_cases i <;> first | exact hfw | exact hft | exact hP | exact hf2 | rfl
  rw [hvec] at hc'
  let := hierarchy_transitive ζ
  have htarget := woodinSparseStageCode_order_certificate_unique hΞ hAC hξ hc' (by
    intro b _ p hp
    apply woodinSparseStageCode_certificate_support hΞ hAC hξ hζ.rankCriterion.2.2.1 _ (subset_hierarchy_rank Q) hp b
    exact ordinal_subset_hierarchy _ ∅ (hζ.regular.2.1 ∅ (by simp))) (succ ζ) (mem_succ_self _)
  have htarget' : (f ‘ O) ‘ (succ ζ) = D := by
    rw [htarget]
    exact sparseCutOrder_succ_rank
      ((woodinSparseStageCode_valid hΞ hAC hξ).system.order.preorder ξ (mem_succ_self ξ))
      (fun _ hp ↦ woodinSparseStageCode_sparse hΞ hAC hξ hp)
  have hv' := (he.bounded_formula_iff boundedValueFormula_bounded ![R, O, succ η]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hrA, hO, h1A])).mp
      ((eval_boundedValueFormula _ _ _).mpr hv.symm)
  have hvec' : (fun i ↦ f ‘ (![R, O, succ η] i)) = ![f ‘ R, f ‘ O, succ ζ] := by
    funext i
    fin_cases i <;> first | rfl | exact hf1
  rw [hvec'] at hv'
  exact ((eval_boundedValueFormula _ _ _).mp hv').trans htarget'

end ZFVP
