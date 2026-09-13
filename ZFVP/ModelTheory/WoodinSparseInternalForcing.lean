import ZFVP.ModelTheory.FiniteRankInternalForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω Ξ θ ξ f n φ b p : V} [IsOrdinal θ] [IsOrdinal ξ]
local notation "P" => (forcingCodeP (woodinSparseStageCode θ)) ‘ θ
local notation "R" => (forcingCodeR (woodinSparseStageCode θ)) ‘ θ
local notation "Q" => (forcingCodeP (woodinSparseStageCode ξ)) ‘ ξ
local notation "S" => (forcingCodeR (woodinSparseStageCode ξ)) ‘ ξ
local notation "η" => rank P
local notation "ζ" => rank Q

theorem woodinSparseStageCode_lowInternalForces_sameCode
    (hΩ : IsWoodinSupercompact Ω) (hΞ : IsWoodinSupercompact Ξ)
    (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hξ : ξ ⊆ Ξ)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd η (ω : V)))
      (hierarchy (ordinalAdd ζ (ω : V))) f)
    (hfP : f ‘ P = Q) (hφ : IsMembershipFormulaCode n φ)
    (hb : b ∈ lowRankNameSet P η ^ n) (hp : p ∈ P) :
    InternalForces P R (lowRankNameSet P η) n φ b p ↔
      InternalForces Q S (lowRankNameSet Q ζ) n φ (f ‘ b) (f ‘ p) := by
  let := hierarchy_transitive (ordinalAdd ζ (ω : V))
  have hη := woodinSparseStageCode_rank_inaccessible hΩ hAC hθ
  have hζ := woodinSparseStageCode_rank_inaccessible hΞ hAC hξ
  have hs : ∀ β ∈ ordinalAdd η (ω : V), succ β ∈ ordinalAdd η (ω : V) :=
    fun _ ↦ ordinalAdd_omega_succ_closed η
  have hpA : P ∈ hierarchy (ordinalAdd η (ω : V)) :=
    (mem_hierarchy_iff_rank_mem _ _).mpr (ordinalAdd_omega_gt η)
  have hfη : f ‘ η = ζ := by
    rw [limitRankEmbedding_value_rank hs he hpA, hfP]
  have hrA := subset_mem_hierarchy_limit hs (prod_mem_hierarchy_limit hs hpA hpA)
    ((woodinSparseStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ)).1
  have hfR := woodinSparseStageCode_order_covariance hΩ hΞ hAC hθ hξ he hfP
  simpa only [hfP, hfR] using finiteRankEmbedding_lowInternalForces_sameCode
    hη hζ he hfη (subset_hierarchy_rank P) hrA hφ hb hp

end ZFVP
