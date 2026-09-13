import ZFVP.ModelTheory.WoodinSparseSourceFiniteRank
import ZFVP.ModelTheory.LimitRankCriticalPoint

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseSourceStageCode_capture_components {A B f γ ξ : V}
    [IsTransitive A] [IsTransitive B]
    (he : IsCodedMembershipEmbedding A B f)
    (hcode : ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ ∈ A)
    (hcap : f ‘ ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ =
      ⟨woodinSparseSourceStageCode ξ, woodinSparseSourceStageCardinals ξ⟩ₖ) :
    f ‘ (woodinSparseSourceStageCode γ) = woodinSparseSourceStageCode ξ ∧
    f ‘ (woodinSparseSourceStageCardinals γ) = woodinSparseSourceStageCardinals ξ := by
  obtain ⟨hs, hK⟩ := kpair_components_mem_transitive hcode
  rw [he.value_pair hs hK hcode] at hcap
  exact ⟨by simpa only [kpair.π₁_kpair] using congrArg kpair.π₁ hcap,
    by simpa only [kpair.π₂_kpair] using congrArg kpair.π₂ hcap⟩

theorem woodinSparseSourceStageCode_capture_cutoff {B f γ ξ i : V}
    [IsOrdinal γ] [IsTransitive B]
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd γ (ω : V))) B f)
    (hcode : ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ ∈
      hierarchy (ordinalAdd γ (ω : V)))
    (hcap : f ‘ ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ =
      ⟨woodinSparseSourceStageCode ξ, woodinSparseSourceStageCardinals ξ⟩ₖ)
    (hi : i ∈ succ (woodinSourceIndex γ)) :
    f ‘ ((woodinSparseSourceStageCardinals γ) ‘ i) =
      (woodinSparseSourceStageCardinals ξ) ‘ (f ‘ i) := by
  let := hierarchy_transitive (ordinalAdd γ (ω : V))
  have hK := (kpair_components_mem_transitive hcode).2
  have ht := woodinSparseSourceStageCardinals_table (θ := γ)
  have hD : succ (woodinSourceIndex γ) ∈ hierarchy (ordinalAdd γ (ω : V)) := by
    simpa only [woodinSourceIndex_successor] using woodinSourceIndex_successor_finiteRank γ
  have hv := he.value_apply hK hD ht.function ht.domain_eq hi
  rw [(woodinSparseSourceStageCode_capture_components he hcode hcap).2] at hv
  exact hv.symm

/-- Endpoint markedness is reflected from the captured actual cutoff table. -/
theorem woodinSparseSourceStageCode_capture_endpoint_fixed
    {Ω Ξ B f γ ξ : V} [IsOrdinal γ] [IsOrdinal ξ] [IsTransitive B]
    (hΩ : IsWoodinSupercompact Ω) (hΞ : IsWoodinSupercompact Ξ)
    (hAC : ¬InternalChoice V) (hγ : γ ⊆ Ω) (hξ : ξ ⊆ Ξ)
    (hγinf : γ ∉ (ω : V)) (hξinf : ξ ∉ (ω : V))
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd γ (ω : V))) B f)
    (hcode : ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ ∈
      hierarchy (ordinalAdd γ (ω : V)))
    (hcap : f ‘ ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ =
      ⟨woodinSparseSourceStageCode ξ, woodinSparseSourceStageCardinals ξ⟩ₖ)
    (himage : f ‘ γ = ξ) (hfix : (kpair.π₂ (woodinIterationRec ξ)) ‘ ξ = ξ) :
    (kpair.π₂ (woodinIterationRec γ)) ‘ γ = γ := by
  let := hierarchy_transitive (ordinalAdd γ (ω : V))
  have hsi := woodinSourceIndex_infinite hγinf
  have hti := woodinSourceIndex_infinite hξinf
  have hv := woodinSparseSourceStageCode_capture_cutoff he hcode hcap
    (i := woodinSourceIndex γ) (mem_succ_self _)
  have htarget : (woodinSparseSourceStageCardinals ξ) ‘ ξ = ξ := by
    have hh := woodinSparseSourceStageCardinals_value hΞ hAC hξ (mem_succ_self ξ)
    simpa only [hti, hfix] using hh
  rw [woodinSparseSourceStageCardinals_value hΩ hAC hγ (mem_succ_self γ), hsi, himage,
    htarget] at hv
  have hK := (kpair_components_mem_transitive hcode).2
  have ht := woodinSparseSourceStageCardinals_table (θ := γ)
  let := ht.function
  have hm := (IsCodedMembershipEmbedding.function_argument_mem hK
    (ht.domain_eq.symm ▸ mem_succ_self (woodinSourceIndex γ))).2
  rw [woodinSparseSourceStageCardinals_value hΩ hAC hγ (mem_succ_self γ)] at hm
  exact IsCodedElementaryEmbedding.value_injective he (by simpa using hm)
    (by simpa using (ordinal_subset_hierarchy _ γ (ordinalAdd_omega_gt γ)))
    (hv.trans himage.symm)

/-- Below the critical point the common actual cutoff entries are fixed. -/
theorem woodinSparseSourceStageCode_capture_cutoff_fixed
    {Ω Ξ B f γ ξ κ i : V} [IsOrdinal γ] [IsOrdinal ξ] [IsTransitive B]
    (hΩ : IsWoodinSupercompact Ω) (hΞ : IsWoodinSupercompact Ξ)
    (hAC : ¬InternalChoice V) (hγ : γ ⊆ Ω) (hξ : ξ ⊆ Ξ)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd γ (ω : V))) B f)
    (hcode : ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ ∈
      hierarchy (ordinalAdd γ (ω : V)))
    (hcap : f ‘ ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ =
      ⟨woodinSparseSourceStageCode ξ, woodinSparseSourceStageCardinals ξ⟩ₖ)
    (hκ : IsCriticalPoint (hierarchy (ordinalAdd γ (ω : V))) f κ)
    (hi : i ∈ κ) (hiγ : i ∈ γ) (hiξ : i ∈ ξ) :
    f ‘ ((kpair.π₂ (woodinIterationRec i)) ‘ i) =
      (kpair.π₂ (woodinIterationRec i)) ‘ i := by
  let := hierarchy_transitive (ordinalAdd γ (ω : V))
  let := hκ.ordinal
  let := IsOrdinal.of_mem hi
  have his : woodinSourceIndex i ∈ κ :=
    woodinSourceIndex_mem_of_mem (fun _ hβ ↦ hκ.succ_closed he hβ) hi
  have hv := woodinSparseSourceStageCode_capture_cutoff he hcode hcap
    (i := woodinSourceIndex i) (by
      rw [← woodinSourceIndex_successor]
      exact woodinSourceIndex_mem_iff.mpr (mem_succ_iff.mpr (Or.inr hiγ)))
  rw [hκ.fixed_below his,
    woodinSparseSourceStageCardinals_value hΩ hAC hγ (mem_succ_iff.mpr (Or.inr hiγ)),
    woodinSparseSourceStageCardinals_value hΞ hAC hξ (mem_succ_iff.mpr (Or.inr hiξ))] at hv
  exact hv

theorem woodinSparseSourceStageCode_capture_cutoffs_below_criticalPoint
    {Ω Ξ B f γ ξ κ : V} [IsOrdinal γ] [IsOrdinal ξ] [IsTransitive B]
    (hΩ : IsWoodinSupercompact Ω) (hΞ : IsWoodinSupercompact Ξ)
    (hAC : ¬InternalChoice V) (hγ : γ ∈ Ω) (hξ : ξ ⊆ Ξ)
    (hγinf : γ ∉ (ω : V)) (hξinf : ξ ∉ (ω : V))
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd γ (ω : V))) B f)
    (hcode : ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ ∈
      hierarchy (ordinalAdd γ (ω : V)))
    (hcap : f ‘ ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ =
      ⟨woodinSparseSourceStageCode ξ, woodinSparseSourceStageCardinals ξ⟩ₖ)
    (himage : f ‘ γ = ξ) (hfix : (kpair.π₂ (woodinIterationRec ξ)) ‘ ξ = ξ)
    (hκ : IsCriticalPoint (hierarchy (ordinalAdd γ (ω : V))) f κ)
    (hκγ : κ ∈ γ) (hκξ : κ ∈ ξ) (hgap : γ ∈ f ‘ κ) :
    ∀ i ∈ κ, (kpair.π₂ (woodinIterationRec i)) ‘ i ∈ κ := by
  let := hΩ.inaccessible.1
  let := hκ.ordinal
  let := hierarchy_transitive (ordinalAdd γ (ω : V))
  let := he.value_ordinal hκ.ordinal hκ.mem_domain
  have hsub : γ ⊆ Ω := IsOrdinal.toIsTransitive.transitive _ hγ
  have hsource := woodinSparseSourceStageCode_capture_endpoint_fixed hΩ hΞ hAC hsub hξ
    hγinf hξinf he hcode hcap himage hfix
  have hinv := woodinSparseSourceStageCode_invariant hΩ hAC hγ
  intro i hi
  let := IsOrdinal.of_mem hi
  have hiγ := IsOrdinal.toIsTransitive.mem_trans hi hκγ
  have hiξ := IsOrdinal.toIsTransitive.mem_trans hi hκξ
  have his : woodinSourceIndex i ∈ succ (woodinSourceIndex γ) :=
    mem_succ_iff.mpr (Or.inr (woodinSourceIndex_mem_iff.mpr hiγ))
  have hb := hinv.increasing (woodinSourceIndex i) his
    (woodinSourceIndex γ) (mem_succ_self _) (woodinSourceIndex_mem_iff.mpr hiγ)
  rw [woodinSparseSourceStageCardinals_value hΩ hAC hsub (mem_succ_iff.mpr (Or.inr hiγ)),
    woodinSparseSourceStageCardinals_value hΩ hAC hsub (mem_succ_self γ), hsource] at hb
  have hci : IsOrdinal ((kpair.π₂ (woodinIterationRec i)) ‘ i) := IsOrdinal.of_mem hb
  let := hci
  apply hκ.fixed_ordinal_below_image he
    (ordinal_subset_hierarchy _ _ (IsOrdinal.toIsTransitive.mem_trans hb (ordinalAdd_omega_gt γ)))
    (woodinSparseSourceStageCode_capture_cutoff_fixed hΩ hΞ hAC hsub hξ he hcode hcap hκ hi hiγ hiξ)
  exact IsOrdinal.toIsTransitive.mem_trans hb hgap

/-- At an inaccessible height, bounds for all earlier actual cutoffs force the
direct branch and its cutoff to equal that height. -/
theorem woodinIterationRec_fixedPoint_of_inaccessible_cutoff_bounds
    {Ω κ : V} (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
    (hκΩ : κ ∈ Ω) (hκ : IsChoicelessInaccessible κ)
    (hb : ∀ i ∈ κ, (kpair.π₂ (woodinIterationRec i)) ‘ i ∈ κ) :
    (kpair.π₂ (woodinIterationRec κ)) ‘ κ = κ := by
  let := hΩ.inaccessible.1
  let := hκ.1
  have hsub : κ ⊆ Ω := IsOrdinal.toIsTransitive.transitive _ hκΩ
  have hp := woodinIterationPrefix_of_stages
    (fun i hi ↦ ((woodinIterationExit hΩ hAC).2.1 i (hsub i hi)).1)
  have hp' : IsWoodinIteration κ κ (woodinIterationPrefix κ)
      (woodinIterationCardinalPrefix κ) := by
    refine ⟨hp.code, hp.cardinals, hp.stage, hp.small, hp.inaccessible, ?_, hp.increasing⟩
    intro i hi
    rw [woodinIterationCardinalPrefix_value hΩ hAC hsub hi]
    exact hb i hi
  have hlim : ∀ i ∈ κ, succ i ∈ κ := fun _ hi ↦ regularCardinal_succ_closed hκ.regular hi
  have he := hp'.limitCardinal_eq_endpoint hlim
  have h0 : κ ≠ ∅ := by
    intro hz
    exact not_mem_empty (hz ▸ hκ.2.1)
  have hn : κ ≠ succ (⋃ˢ κ) := by
    intro hz
    have hm : ⋃ˢ κ ∈ κ := (congrArg (fun x : V ↦ (⋃ˢ κ) ∈ x) hz).mpr (mem_succ_self _)
    have hh := hlim _ hm
    rw [← hz] at hh
    exact mem_irrefl _ hh
  rw [woodinIterationRec_direct h0 hn (he.symm ▸ hκ), kpair.π₂_kpair,
    forcingFamilyNext_new, he]

/-- Markedness at the source, critical point, and its image is a consequence of
the complete-code equation in the restricted lifting hypotheses. -/
theorem woodinSparseSourceStageCode_capture_marked
    {Ω f γ ξ κ : V} [IsOrdinal γ] [IsOrdinal ξ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hξ : ξ ∈ Ω)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd γ (ω : V)))
      (hierarchy (ordinalAdd ξ (ω : V))) f)
    (hcode : ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ ∈
      hierarchy (ordinalAdd γ (ω : V)))
    (hcap : f ‘ ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ =
      ⟨woodinSparseSourceStageCode ξ, woodinSparseSourceStageCardinals ξ⟩ₖ)
    (himage : f ‘ γ = ξ) (hfix : (kpair.π₂ (woodinIterationRec ξ)) ‘ ξ = ξ)
    (hκ : IsCriticalPoint (hierarchy (ordinalAdd γ (ω : V))) f κ)
    (hκγ : κ ∈ γ) (hgap : γ ∈ f ‘ κ) :
    (kpair.π₂ (woodinIterationRec γ)) ‘ γ = γ ∧
    (kpair.π₂ (woodinIterationRec κ)) ‘ κ = κ ∧
    (kpair.π₂ (woodinIterationRec (f ‘ κ))) ‘ (f ‘ κ) = f ‘ κ ∧
    IsChoicelessInaccessible γ ∧ IsChoicelessInaccessible κ ∧
    IsChoicelessInaccessible (f ‘ κ) ∧
    (∀ i ∈ κ, (kpair.π₂ (woodinIterationRec i)) ‘ i ∈ κ) ∧
    (∀ x ∈ hierarchy κ, f ‘ x = x) := by
  let := hΩ.inaccessible.1
  let := hκ.ordinal
  let := hierarchy_transitive (ordinalAdd γ (ω : V))
  let := hierarchy_transitive (ordinalAdd ξ (ω : V))
  let := he.value_ordinal hκ.ordinal hκ.mem_domain
  have hγA : γ ∈ hierarchy (ordinalAdd γ (ω : V)) :=
    ordinal_subset_hierarchy _ _ (ordinalAdd_omega_gt γ)
  have hδξ : f ‘ κ ∈ ξ := by
    rw [← himage]
    exact (he.value_mem_iff hκ.mem_domain hγA).mpr hκγ
  have hγξ : γ ∈ ξ := IsOrdinal.toIsTransitive.mem_trans hgap hδξ
  have hγΩ := IsOrdinal.toIsTransitive.mem_trans hγξ hξ
  have hκξ := IsOrdinal.toIsTransitive.mem_trans hκγ hγξ
  have hκΩ := IsOrdinal.toIsTransitive.mem_trans hκγ hγΩ
  have hδΩ := IsOrdinal.toIsTransitive.mem_trans hδξ hξ
  have hωγ : (ω : V) ∈ γ := by
    rcases IsOrdinal.subset_iff.mp (hκ.omega_subset he) with heq | hl
    · exact heq.symm ▸ hκγ
    · exact IsOrdinal.toIsTransitive.mem_trans hl hκγ
  have hωξ := IsOrdinal.toIsTransitive.mem_trans hωγ hγξ
  have hγinf : γ ∉ (ω : V) := fun hh ↦ mem_asymm hh hωγ
  have hξinf : ξ ∉ (ω : V) := fun hh ↦ mem_asymm hh hωξ
  have hsubγ : γ ⊆ Ω := IsOrdinal.toIsTransitive.transitive _ hγΩ
  have hsubξ : ξ ⊆ Ω := IsOrdinal.toIsTransitive.transitive _ hξ
  have hsource := woodinSparseSourceStageCode_capture_endpoint_fixed hΩ hΩ hAC hsubγ hsubξ
    hγinf hξinf he hcode hcap himage hfix
  have hb := woodinSparseSourceStageCode_capture_cutoffs_below_criticalPoint hΩ hΩ hAC hγΩ hsubξ
    hγinf hξinf he hcode hcap himage hfix hκ hκγ hκξ hgap
  have hlim : ∀ β ∈ ordinalAdd γ (ω : V), succ β ∈ ordinalAdd γ (ω : V) :=
    fun _ hh ↦ ordinalAdd_omega_succ_closed γ hh
  have hinac := limitRankEmbedding_criticalPoint_inaccessible hlim he hκ
    (ordinal_subset_hierarchy _ _ (IsOrdinal.toIsTransitive.mem_trans hωγ (ordinalAdd_omega_gt γ)))
  have hefix := woodinIterationRec_fixedPoint_of_inaccessible_cutoff_bounds hΩ hAC hκΩ hinac hb
  have hκinf : κ ∉ (ω : V) := fun hh ↦ mem_asymm hh hinac.2.1
  have hδinf : f ‘ κ ∉ (ω : V) := fun hh ↦ mem_asymm hh
    (IsOrdinal.toIsTransitive.mem_trans hinac.2.1 (hκ.lt_value he))
  have hsi := woodinSourceIndex_infinite hκinf
  have hti := woodinSourceIndex_infinite hδinf
  have hv := woodinSparseSourceStageCode_capture_cutoff he hcode hcap
    (i := woodinSourceIndex κ) (by
      rw [← woodinSourceIndex_successor]
      exact woodinSourceIndex_mem_iff.mpr (mem_succ_iff.mpr (Or.inr hκγ)))
  have ht : (woodinSparseSourceStageCardinals ξ) ‘ (f ‘ κ) =
      (kpair.π₂ (woodinIterationRec (f ‘ κ))) ‘ (f ‘ κ) := by
    have hh := woodinSparseSourceStageCardinals_value hΩ hAC hsubξ
      (mem_succ_iff.mpr (Or.inr hδξ))
    simpa only [hti] using hh
  rw [woodinSparseSourceStageCardinals_value hΩ hAC hsubγ
    (mem_succ_iff.mpr (Or.inr hκγ)), hefix, hsi, ht] at hv
  have hδfix := hv.symm
  have hγinac : IsChoicelessInaccessible γ :=
    hsource ▸ ((woodinIterationExit hΩ hAC).2.1 γ hγΩ).1.inaccessible γ (mem_succ_self γ)
  have hδinac : IsChoicelessInaccessible (f ‘ κ) :=
    hδfix ▸ ((woodinIterationExit hΩ hAC).2.1 (f ‘ κ) hδΩ).1.inaccessible (f ‘ κ) (mem_succ_self _)
  exact ⟨hsource, hefix, hδfix, hγinac, hinac, hδinac, hb,
    limitRankEmbedding_fixed_below_criticalPoint hlim he hκ⟩

end ZFVP
