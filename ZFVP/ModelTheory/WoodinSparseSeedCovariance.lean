import ZFVP.ModelTheory.WoodinSparseFiniteSeedCertificate
import ZFVP.ModelTheory.LimitRankEmbeddingAction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω Ξ θ ξ f : V} [IsOrdinal θ] [IsOrdinal ξ]
local notation "P" => (forcingCodeP (woodinSparseStageCode θ)) ‘ θ
local notation "Q" => (forcingCodeP (woodinSparseStageCode ξ)) ‘ ξ
local notation "η" => rank P
local notation "ζ" => rank Q
local notation "A" => hierarchy (ordinalAdd η (ω : V))
local notation "B" => hierarchy (ordinalAdd ζ (ω : V))

theorem woodinSparseStageCode_seed_covariance
    (hΩ : IsWoodinSupercompact Ω) (hΞ : IsWoodinSupercompact Ξ)
    (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hξ : ξ ⊆ Ξ)
    (he : IsCodedMembershipEmbedding A B f) (hP : f ‘ P = Q) :
    f ‘ (woodinSeedCardinal : V) = woodinSeedCardinal := by
  let := hierarchy_transitive (ordinalAdd η (ω : V))
  let := hierarchy_transitive (ordinalAdd ζ (ω : V))
  have hη := woodinSparseStageCode_rank_inaccessible hΩ hAC hθ
  have hδ : ∀ β ∈ ordinalAdd η (ω : V), succ β ∈ ordinalAdd η (ω : V) :=
    fun _ hb ↦ ordinalAdd_omega_succ_closed η hb
  have hε : ∀ β ∈ ordinalAdd ζ (ω : V), succ β ∈ ordinalAdd ζ (ω : V) :=
    fun _ hb ↦ ordinalAdd_omega_succ_closed ζ hb
  have hηδ := ordinalAdd_omega_gt η
  have hpA : P ∈ A := (mem_hierarchy_iff_rank_mem _ _).mpr hηδ
  have hηA : η ∈ A := ordinal_subset_hierarchy _ _ hηδ
  have htA : hierarchy η ∈ A := hierarchy_mem hηδ
  have hfη : f ‘ η = ζ := by
    rw [limitRankEmbedding_value_rank hδ he hpA, hP]
  have hft : f ‘ (hierarchy η) = hierarchy ζ := by
    rw [(limitRankEmbedding_value_hierarchy hδ hε he inferInstance hηA).2, hfη]
  have hzero : (∅ : V) ∈ η := hη.regular.2.1 ∅ (by simp)
  have h0A : (∅ : V) ∈ A := ordinal_subset_hierarchy _ _
    (IsOrdinal.toIsTransitive.mem_trans hzero hηδ)
  have hoA : succ (∅ : V) ∈ A := ordinal_subset_hierarchy _ _
    (hδ _ (IsOrdinal.toIsTransitive.mem_trans hzero hηδ))
  have hfo : f ‘ (succ (∅ : V)) = succ (∅ : V) := by
    rw [he.value_succ h0A hoA, he.value_empty h0A]
  obtain ⟨hmA, F, hF, W, hW, C, hC, hc⟩ :=
    woodinSparseStageCode_finite_seed_certificate hΩ hAC hθ
  have hparams : ∀ i, (![P, hierarchy η, succ (∅ : V), F, W, C, woodinSeedCardinal] i) ∈ A := by
    intro i
    fin_cases i <;> assumption
  have hc' := (he.bounded_formula_iff boundedSparseSeedCertificateFormula_bounded
    ![P, hierarchy η, succ (∅ : V), F, W, C, woodinSeedCardinal] hparams).mp hc
  have hvec : (fun i ↦ f ‘ (![P, hierarchy η, succ (∅ : V), F, W, C, woodinSeedCardinal] i)) =
      ![Q, hierarchy ζ, succ (∅ : V), f ‘ F, f ‘ W, f ‘ C, f ‘ woodinSeedCardinal] := by
    funext i
    fin_cases i <;> first | exact hP | exact hft | exact hfo | rfl
  rw [hvec] at hc'
  let := hierarchy_transitive ζ
  exact (boundedSparseSeedCertificate_unique hc').trans
    (woodinSparseStageCode_seed_from_carrier hΞ hAC hξ)

end ZFVP
