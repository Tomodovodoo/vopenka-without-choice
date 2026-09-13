import ZFVP.ModelTheory.BoundedCoordinatePool
import ZFVP.ModelTheory.SparseCutCovariance

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCodedMembershipEmbedding.value_sparseCoordinatePool {A B f S a : V}
    [IsTransitive A] [IsTransitive B] (he : IsCodedMembershipEmbedding A B f)
    (hS : S ∈ A) (ha : a ∈ A) (hW : sparseCoordinatePool S a ∈ A) :
    f ‘ (sparseCoordinatePool S a) = sparseCoordinatePool (f ‘ S) (f ‘ a) := by
  have hh := (he.bounded_formula_iff boundedCoordinatePoolFormula_bounded
    ![sparseCoordinatePool S a, S, a]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hW, hS, ha])).mp
      (eval_boundedCoordinatePoolFormula.mpr rfl)
  have hv : (fun i ↦ f ‘ (![sparseCoordinatePool S a, S, a] i)) =
      ![f ‘ (sparseCoordinatePool S a), f ‘ S, f ‘ a] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at hh
  exact eval_boundedCoordinatePoolFormula.mp hh

variable {Ω θ ξ f a : V} [IsOrdinal θ]
local notation "P" => (forcingCodeP (woodinSparseStageCode θ)) ‘ θ
local notation "Q" => (forcingCodeP (woodinSparseStageCode ξ)) ‘ ξ
local notation "η" => rank P
local notation "ζ" => rank Q

theorem woodinSparseStageCode_pool_covariance
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd η (ω : V)))
      (hierarchy (ordinalAdd ζ (ω : V))) f) (hP : f ‘ P = Q)
    (ha : a ∈ hierarchy (ordinalAdd η (ω : V))) :
    f ‘ (sparseCoordinatePool P a) = sparseCoordinatePool Q (f ‘ a) := by
  let := hierarchy_transitive (ordinalAdd η (ω : V))
  let := hierarchy_transitive (ordinalAdd ζ (ω : V))
  have hη := woodinSparseStageCode_rank_inaccessible hΩ hAC hθ
  have h0 : (∅ : V) ∈ hierarchy η := ordinal_subset_hierarchy _ ∅ (hη.regular.2.1 ∅ (by simp))
  have hpA : P ∈ hierarchy (ordinalAdd η (ω : V)) :=
    (mem_hierarchy_iff_rank_mem _ _).mpr (ordinalAdd_omega_gt η)
  have hW : sparseCoordinatePool P a ∈ hierarchy (ordinalAdd η (ω : V)) := by
    apply mem_hierarchy_of_mem_stage (ordinalAdd_omega_succ_closed η (ordinalAdd_omega_gt η))
    rw [hierarchy_succ, mem_power_iff]
    intro τ hτ
    obtain ⟨p, hp, rfl⟩ := mem_sparseCoordinatePool_iff.mp hτ
    exact (woodinSparseStageCode_certificate_support hΩ hAC hθ hη.rankCriterion.2.2.1
      h0 (subset_hierarchy_rank P) hp a).2
  rw [← hP]
  exact he.value_sparseCoordinatePool hpA ha hW

end ZFVP
