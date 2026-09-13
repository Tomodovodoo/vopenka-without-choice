import ZFVP.ModelTheory.BoundedLowNameFamily
import ZFVP.ModelTheory.LimitRankEmbeddingAction
import ZFVP.ModelTheory.WoodinSparseOrderCovariance

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCodedMembershipEmbedding.value_lowRankNameSet {A B f P η ζ : V}
    [IsTransitive A] [IsTransitive B] [IsOrdinal η] [IsOrdinal ζ]
    (he : IsCodedMembershipEmbedding A B f) (hP : P ∈ A)
    (hT : hierarchy η ∈ A) (hN : lowRankNameSet P η ∈ A)
    (hTimage : f ‘ (hierarchy η) = hierarchy ζ) :
    f ‘ (lowRankNameSet P η) = lowRankNameSet (f ‘ P) ζ := by
  have hh := (he.bounded_formula_iff boundedLowNameFamilyFormula_bounded
    ![P, hierarchy η, lowRankNameSet P η]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hP, hT, hN])).mp
      (boundedLowNameFamily_rank_iff.mpr rfl)
  have hv : (fun i ↦ f ‘ (![P, hierarchy η, lowRankNameSet P η] i)) =
      ![f ‘ P, f ‘ (hierarchy η), f ‘ (lowRankNameSet P η)] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, hTimage] at hh
  exact boundedLowNameFamily_rank_iff.mp hh

theorem limitRankEmbedding_value_lowRankNameSet {δ ε f P η : V}
    [IsOrdinal δ] [IsOrdinal ε] [IsOrdinal η]
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hε : ∀ β ∈ ε, succ β ∈ ε)
    (he : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hP : P ∈ hierarchy δ) (hη : η ∈ δ) :
    f ‘ (lowRankNameSet P η) = lowRankNameSet (f ‘ P) (f ‘ η) := by
  let := hierarchy_transitive δ
  let := hierarchy_transitive ε
  have hact := limitRankEmbedding_value_hierarchy hδ hε he inferInstance
    (ordinal_subset_hierarchy δ η hη)
  let := hact.1
  have hN : lowRankNameSet P η ∈ hierarchy δ := by
    apply mem_hierarchy_of_mem_stage (hδ η hη)
    rw [hierarchy_succ, mem_power_iff]
    exact lowRankNameSet_subset P η
  exact he.value_lowRankNameSet hP (hierarchy_mem hη) hN hact.2

variable {θ ξ f : V}
local notation "P" => (forcingCodeP (woodinSparseStageCode θ)) ‘ θ
local notation "Q" => (forcingCodeP (woodinSparseStageCode ξ)) ‘ ξ
local notation "η" => rank P
local notation "ζ" => rank Q

theorem woodinSparseStageCode_lowName_covariance
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd η (ω : V)))
      (hierarchy (ordinalAdd ζ (ω : V))) f) (hP : f ‘ P = Q) :
    f ‘ (lowRankNameSet P η) = lowRankNameSet Q ζ := by
  let := hierarchy_transitive (ordinalAdd ζ (ω : V))
  have hδ : ∀ β ∈ ordinalAdd η (ω : V), succ β ∈ ordinalAdd η (ω : V) :=
    fun _ hb ↦ ordinalAdd_omega_succ_closed η hb
  have hε : ∀ β ∈ ordinalAdd ζ (ω : V), succ β ∈ ordinalAdd ζ (ω : V) :=
    fun _ hb ↦ ordinalAdd_omega_succ_closed ζ hb
  have hp : P ∈ hierarchy (ordinalAdd η (ω : V)) :=
    (mem_hierarchy_iff_rank_mem _ _).mpr (ordinalAdd_omega_gt η)
  have hfη : f ‘ η = ζ := by
    rw [limitRankEmbedding_value_rank hδ he hp, hP]
  rw [limitRankEmbedding_value_lowRankNameSet hδ hε he hp (ordinalAdd_omega_gt η), hP, hfη]

end ZFVP
