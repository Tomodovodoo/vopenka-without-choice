import ZFVP.ModelTheory.SuccessorLowNameCovariance
import ZFVP.ModelTheory.BoundedSetForcingCovariance

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem finiteRankEmbedding_successorNameForcing_iff {η ζ f P Q R S p : V}
    [IsOrdinal η] [IsOrdinal ζ]
    (hη : ∀ β ∈ η, succ β ∈ η) (hζ : ∀ β ∈ ζ, succ β ∈ ζ)
    (hP : P ⊆ hierarchy η) (hQ : Q ⊆ hierarchy ζ) (hR : R ⊆ P ×ˢ P)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd η (ω : V)))
      (hierarchy (ordinalAdd ζ (ω : V))) f)
    (hfP : f ‘ P = Q) (hfR : f ‘ R = S) (hfη : f ‘ η = ζ) (hp : p ∈ P)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V)
    (hv : ∀ i, v i ∈ successorLowNameSet P η) :
    p ∈ classForcingFormula P R (fun x ↦ x ∈ successorLowNameSet P η) (by definability)
      φ (standardTuple v) ↔
      f ‘ p ∈ classForcingFormula Q S (fun x ↦ x ∈ successorLowNameSet Q ζ) (by definability)
        φ (standardTuple (fun i ↦ f ‘ (v i))) := by
  let := hierarchy_transitive (ordinalAdd η (ω : V))
  let := hierarchy_transitive (ordinalAdd ζ (ω : V))
  let := hierarchy_transitive (succ η)
  have hs : ∀ β ∈ ordinalAdd η (ω : V), succ β ∈ ordinalAdd η (ω : V) :=
    fun _ ↦ ordinalAdd_omega_succ_closed η
  have hpA : P ∈ hierarchy (ordinalAdd η (ω : V)) := by
    apply mem_hierarchy_of_mem_stage (hs _ (ordinalAdd_omega_gt η))
    rwa [hierarchy_succ, mem_power_iff]
  have hrA := subset_mem_hierarchy_limit hs (prod_mem_hierarchy_limit hs hpA hpA) hR
  have hD := finiteRankEmbedding_value_successorLowNameSet hη hζ hP hQ he hfP hfη
  have ht := limitRankEmbedding_setForcing_iff hs he
    (hierarchy_mem (hs _ (ordinalAdd_omega_gt η))) hpA hrA
    (successorLowNameSet_mem_finite_rank hη hP) (successorLowNameSet_subset_hierarchy hη hP)
    ((hierarchy_transitive _).mem_trans hp hpA) φ v hv
  rwa [hfP, hfR, hD] at ht

variable {Ω Ξ θ ξ f p : V} [IsOrdinal θ] [IsOrdinal ξ]
local notation "P" => (forcingCodeP (woodinSparseStageCode θ)) ‘ θ
local notation "R" => (forcingCodeR (woodinSparseStageCode θ)) ‘ θ
local notation "Q" => (forcingCodeP (woodinSparseStageCode ξ)) ‘ ξ
local notation "S" => (forcingCodeR (woodinSparseStageCode ξ)) ‘ ξ
local notation "η" => rank P
local notation "ζ" => rank Q

theorem woodinSparseStageCode_successorNameForcing_iff
    (hΩ : IsWoodinSupercompact Ω) (hΞ : IsWoodinSupercompact Ξ)
    (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hξ : ξ ⊆ Ξ)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd η (ω : V)))
      (hierarchy (ordinalAdd ζ (ω : V))) f) (hP : f ‘ P = Q) (hp : p ∈ P)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V)
    (hv : ∀ i, v i ∈ successorLowNameSet P η) :
    p ∈ classForcingFormula P R (fun x ↦ x ∈ successorLowNameSet P η) (by definability)
      φ (standardTuple v) ↔
      f ‘ p ∈ classForcingFormula Q S (fun x ↦ x ∈ successorLowNameSet Q ζ) (by definability)
        φ (standardTuple (fun i ↦ f ‘ (v i))) := by
  let := hierarchy_transitive (ordinalAdd ζ (ω : V))
  have hη := woodinSparseStageCode_rank_inaccessible hΩ hAC hθ
  have hζ := woodinSparseStageCode_rank_inaccessible hΞ hAC hξ
  have hpA : P ∈ hierarchy (ordinalAdd η (ω : V)) :=
    (mem_hierarchy_iff_rank_mem _ _).mpr (ordinalAdd_omega_gt η)
  have hfη : f ‘ η = ζ := by
    rw [limitRankEmbedding_value_rank (fun _ ↦ ordinalAdd_omega_succ_closed η) he hpA, hP]
  exact finiteRankEmbedding_successorNameForcing_iff hη.rankCriterion.2.2.1 hζ.rankCriterion.2.2.1
    (subset_hierarchy_rank P) (subset_hierarchy_rank Q)
    ((woodinSparseStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ)).1
    he hP (woodinSparseStageCode_order_covariance hΩ hΞ hAC hθ hξ he hP) hfη hp φ v hv

end ZFVP
