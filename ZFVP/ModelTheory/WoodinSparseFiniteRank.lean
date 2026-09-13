import ZFVP.ModelTheory.WoodinSparseMarkedRank
import ZFVP.ModelTheory.ForcingRecodedFiniteRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω γ : V} [IsOrdinal γ]

theorem woodinSparseStageCode_finiteRank_of_rows
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hγ : γ ⊆ Ω)
    (hP : ∀ i ∈ succ γ, (forcingCodeP (woodinSparseStageCode γ)) ‘ i ⊆ hierarchy γ) :
    woodinSparseStageCode γ ∈ hierarchy (ordinalAdd γ (ω : V)) := by
  have hc := woodinSparseStageCode_valid hΩ hAC hγ
  have hm := woodinSparseStageCode_family hΩ hAC hγ
  have hidx : succ γ ∈ hierarchy (ordinalAdd γ (ω : V)) := by
    rw [mem_hierarchy_iff_rank_mem, rank_of_ordinal]
    exact ordinalAdd_omega_succ_closed γ (ordinalAdd_omega_gt γ)
  have hh := hc.finiteRank (γ := γ) hidx hP
  simp only [woodinSparseStageCode, forcingRecodedCode, forcingCodeP_code, forcingCodeR_code,
    forcingCodeπ_code, forcingCodeE_code, forcingCodeL_code, forcingCodet_code] at hh ⊢
  exact hh (fun i hi j hj ↦ forcingRecodedProjections_graph_bound hm hi hj)
    (fun i hi j hj ↦ forcingRecodedSections_graph_bound hm hi hj)
    (fun i hi j hj ↦ forcingRecodedLifts_graph_bound hm hi hj)

theorem woodinSparseStageCode_finiteRank_at_fixedPoint
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hγ : γ ∈ Ω)
    (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ) :
    woodinSparseStageCode γ ∈ hierarchy (ordinalAdd γ (ω : V)) := by
  let := hΩ.inaccessible.1
  exact woodinSparseStageCode_finiteRank_of_rows hΩ hAC
    (IsOrdinal.toIsTransitive.transitive _ hγ)
    (woodinSparseStageCode_rows_subset_at_fixedPoint hΩ hAC hγ hfix)

theorem woodinSparseStageCode_finiteRank_at_endpoint
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    woodinSparseStageCode Ω ∈ hierarchy (ordinalAdd Ω (ω : V)) := by
  let := hΩ.inaccessible.1
  exact woodinSparseStageCode_finiteRank_of_rows hΩ hAC (subset_refl Ω)
    (woodinSparseStageCode_rows_subset_at_endpoint hΩ hAC)

theorem woodinIterationRec_cardinals_subset_at_fixedPoint
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hγ : γ ∈ Ω)
    (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ) :
    ∀ i ∈ succ γ, (kpair.π₂ (woodinIterationRec γ)) ‘ i ⊆ γ := by
  let := hΩ.inaccessible.1
  intro i hi
  rcases mem_succ_iff.mp hi with he | hi
  · subst i
    rw [woodinIteration_fixedPoint_cardinal hΩ hAC hγ hfix]
  · rw [woodinIterationRec_old_cardinal hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hγ)
      (mem_succ_iff.mpr (Or.inr hi)),
      ← woodinIterationCardinalPrefix_value hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hγ) hi]
    exact IsOrdinal.toIsTransitive.transitive _
      ((woodinIteration_fixedPoint_prefix hΩ hAC hγ hfix).bounded i hi)

theorem woodinIterationRec_cardinals_subset_at_endpoint
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    ∀ i ∈ succ Ω, (kpair.π₂ (woodinIterationRec Ω)) ‘ i ⊆ Ω := by
  let := hΩ.inaccessible.1
  intro i hi
  rcases mem_succ_iff.mp hi with he | hi
  · subst i
    rw [woodinIteration_endpoint_cardinal hΩ hAC]
  · rw [woodinIterationRec_old_cardinal hΩ hAC (subset_refl Ω) (mem_succ_iff.mpr (Or.inr hi)),
      ← woodinIterationCardinalPrefix_value hΩ hAC (subset_refl Ω) hi]
    exact IsOrdinal.toIsTransitive.transitive _ ((woodinIterationExit hΩ hAC).2.2.1.bounded i hi)

theorem woodinSparseStageCode_pair_finiteRank_of_rows
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hγ : γ ⊆ Ω)
    (hP : ∀ i ∈ succ γ, (forcingCodeP (woodinSparseStageCode γ)) ‘ i ⊆ hierarchy γ)
    (hK : ∀ i ∈ succ γ, (kpair.π₂ (woodinIterationRec γ)) ‘ i ⊆ γ) :
    ⟨woodinSparseStageCode γ, kpair.π₂ (woodinIterationRec γ)⟩ₖ ∈
      hierarchy (ordinalAdd γ (ω : V)) := by
  have ht : IsIterationTable (succ γ) (kpair.π₂ (woodinIterationRec γ)) := by
    let := hΩ.inaccessible.1
    rcases IsOrdinal.subset_iff.mp hγ with he | hγ
    · subst Ω
      exact (woodinIteration_endpoint_valid hΩ hAC).1.cardinals
    · exact ((woodinIterationExit hΩ hAC).2.1 γ hγ).1.cardinals
  have hidx : succ γ ∈ hierarchy (ordinalAdd γ (ω : V)) := by
    rw [mem_hierarchy_iff_rank_mem, rank_of_ordinal]
    exact ordinalAdd_omega_succ_closed γ (ordinalAdd_omega_gt γ)
  exact kpair_mem_hierarchy_limit (fun _ h ↦ ordinalAdd_omega_succ_closed γ h)
    (woodinSparseStageCode_finiteRank_of_rows hΩ hAC hγ hP) (ht.cutoff_finiteRank hidx hK)

theorem woodinSparseStageCode_pair_finiteRank_at_fixedPoint
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hγ : γ ∈ Ω)
    (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ) :
    ⟨woodinSparseStageCode γ, kpair.π₂ (woodinIterationRec γ)⟩ₖ ∈
      hierarchy (ordinalAdd γ (ω : V)) := by
  let := hΩ.inaccessible.1
  exact woodinSparseStageCode_pair_finiteRank_of_rows hΩ hAC
    (IsOrdinal.toIsTransitive.transitive _ hγ)
    (woodinSparseStageCode_rows_subset_at_fixedPoint hΩ hAC hγ hfix)
    (woodinIterationRec_cardinals_subset_at_fixedPoint hΩ hAC hγ hfix)

theorem woodinSparseStageCode_pair_finiteRank_at_endpoint
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    ⟨woodinSparseStageCode Ω, kpair.π₂ (woodinIterationRec Ω)⟩ₖ ∈
      hierarchy (ordinalAdd Ω (ω : V)) := by
  let := hΩ.inaccessible.1
  exact woodinSparseStageCode_pair_finiteRank_of_rows hΩ hAC (subset_refl Ω)
    (woodinSparseStageCode_rows_subset_at_endpoint hΩ hAC)
    (woodinIterationRec_cardinals_subset_at_endpoint hΩ hAC)

end ZFVP

