import ZFVP.ModelTheory.WoodinSparseFiniteRank
import ZFVP.ModelTheory.WoodinSourceFiniteRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω γ : V} [IsOrdinal γ]

theorem woodinSourceIndex_successor_finiteRank (γ : V) [IsOrdinal γ] :
    woodinSourceIndex (succ γ) ∈ hierarchy (ordinalAdd γ (ω : V)) := by
  rw [mem_hierarchy_iff_rank_mem, rank_of_ordinal]
  exact woodinSourceIndex_mem_of_mem (fun _ h ↦ ordinalAdd_omega_succ_closed γ h)
    (ordinalAdd_omega_succ_closed γ (ordinalAdd_omega_gt γ))

theorem woodinSparseSourceStageCode_finiteRank_of_rows
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hγ : γ ⊆ Ω)
    (hP : ∀ i ∈ succ γ, (forcingCodeP (woodinSparseStageCode γ)) ‘ i ⊆ hierarchy γ) :
    woodinSparseSourceStageCode γ ∈ hierarchy (ordinalAdd γ (ω : V)) := by
  apply woodinSourceCode_finiteRank (woodinSourceIndex_successor_finiteRank γ)
    (woodinSparseStageCode_valid hΩ hAC hγ)
  simpa only [woodinSparseStageCode, forcingRecodedCode, forcingCodeP_code, forcingCodeR_code,
    forcingCodeπ_code, forcingCodeE_code, forcingCodeL_code, forcingCodet_code] using
    woodinSparseStageCode_finiteRank_of_rows hΩ hAC hγ hP

theorem woodinSparseSourceStageCode_pair_finiteRank_of_rows
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hγ : γ ⊆ Ω)
    (hP : ∀ i ∈ succ γ, (forcingCodeP (woodinSparseStageCode γ)) ‘ i ⊆ hierarchy γ)
    (hK : ∀ i ∈ succ γ, (kpair.π₂ (woodinIterationRec γ)) ‘ i ⊆ γ) :
    ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ ∈
      hierarchy (ordinalAdd γ (ω : V)) := by
  let := hΩ.inaccessible.1
  have ht : IsIterationTable (succ γ) (kpair.π₂ (woodinIterationRec γ)) := by
    rcases IsOrdinal.subset_iff.mp hγ with he | hγ
    · subst Ω
      exact (woodinIteration_endpoint_valid hΩ hAC).1.cardinals
    · exact ((woodinIterationExit hΩ hAC).2.1 γ hγ).1.cardinals
  have h0 : (∅ : V) ∈ succ γ := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (empty_subset γ))
  have hμγ : (woodinSeedCardinal : V) ∈ γ := hK ∅ h0 _ (woodinIterationRec_seed_cardinal_lt hΩ hAC hγ)
  let := IsOrdinal.of_mem hμγ
  apply woodinSourceCode_pair_mem_hierarchy (fun _ h ↦ ordinalAdd_omega_succ_closed γ h)
    (woodinSourceIndex_successor_finiteRank γ) (woodinSparseStageCode_valid hΩ hAC hγ) ht
  · simpa only [woodinSparseStageCode, forcingRecodedCode, forcingCodeP_code, forcingCodeR_code,
      forcingCodeπ_code, forcingCodeE_code, forcingCodeL_code, forcingCodet_code] using
      woodinSparseStageCode_pair_finiteRank_of_rows hΩ hAC hγ hP hK
  · exact ordinal_subset_hierarchy _ _ (IsOrdinal.toIsTransitive.mem_trans hμγ (ordinalAdd_omega_gt γ))

theorem woodinSparseSourceStageCode_finiteRank_at_fixedPoint
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hγ : γ ∈ Ω)
    (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ) :
    woodinSparseSourceStageCode γ ∈ hierarchy (ordinalAdd γ (ω : V)) := by
  let := hΩ.inaccessible.1
  exact woodinSparseSourceStageCode_finiteRank_of_rows hΩ hAC
    (IsOrdinal.toIsTransitive.transitive _ hγ)
    (woodinSparseStageCode_rows_subset_at_fixedPoint hΩ hAC hγ hfix)

theorem woodinSparseSourceStageCode_finiteRank_at_endpoint
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    woodinSparseSourceStageCode Ω ∈ hierarchy (ordinalAdd Ω (ω : V)) := by
  let := hΩ.inaccessible.1
  exact woodinSparseSourceStageCode_finiteRank_of_rows hΩ hAC (subset_refl Ω)
    (woodinSparseStageCode_rows_subset_at_endpoint hΩ hAC)

theorem woodinSparseSourceStageCode_pair_finiteRank_at_fixedPoint
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hγ : γ ∈ Ω)
    (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ) :
    ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ ∈
      hierarchy (ordinalAdd γ (ω : V)) := by
  let := hΩ.inaccessible.1
  exact woodinSparseSourceStageCode_pair_finiteRank_of_rows hΩ hAC
    (IsOrdinal.toIsTransitive.transitive _ hγ)
    (woodinSparseStageCode_rows_subset_at_fixedPoint hΩ hAC hγ hfix)
    (woodinIterationRec_cardinals_subset_at_fixedPoint hΩ hAC hγ hfix)

theorem woodinSparseSourceStageCode_pair_finiteRank_at_endpoint
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    ⟨woodinSparseSourceStageCode Ω, woodinSparseSourceStageCardinals Ω⟩ₖ ∈
      hierarchy (ordinalAdd Ω (ω : V)) := by
  let := hΩ.inaccessible.1
  exact woodinSparseSourceStageCode_pair_finiteRank_of_rows hΩ hAC (subset_refl Ω)
    (woodinSparseStageCode_rows_subset_at_endpoint hΩ hAC)
    (woodinIterationRec_cardinals_subset_at_endpoint hΩ hAC)

end ZFVP
