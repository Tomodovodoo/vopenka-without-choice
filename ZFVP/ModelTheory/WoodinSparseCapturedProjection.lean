import ZFVP.ModelTheory.WoodinSparseCapturedCutoffs
import ZFVP.ModelTheory.SparseOperationCovariance

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinIterationRec_cardinal_eq_endpoint {Ω i : V} [IsOrdinal i]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hi : i ∈ succ Ω) :
    (kpair.π₂ (woodinIterationRec i)) ‘ i = (kpair.π₂ (woodinIterationRec Ω)) ‘ i := by
  let := hΩ.inaccessible.1
  have hv := woodinSparseSourceStageCardinals_value hΩ hAC (subset_refl Ω) hi
  rw [woodinSparseSourceStageCardinals, woodinSourceCardinals_stage hi] at hv
  exact hv.symm

theorem woodinSparseSourceStageCode_pair_first (γ : V) :
    woodinSparseSourceStageCode γ =
      ⟨forcingCodeP (woodinSparseSourceStageCode γ), kpair.π₂ (woodinSparseSourceStageCode γ)⟩ₖ := by
  simp only [woodinSparseSourceStageCode, woodinSourceCode, forcingIterationCode,
    forcingCodeP, kpair.π₁_kpair, kpair.π₂_kpair]

theorem woodinSparseSourceStageCode_capture_carrier {Ω B f γ ξ i : V}
    [IsOrdinal γ] [IsTransitive B]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hγ : γ ⊆ Ω)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd γ (ω : V))) B f)
    (hcode : ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ ∈
      hierarchy (ordinalAdd γ (ω : V)))
    (hcap : f ‘ ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ =
      ⟨woodinSparseSourceStageCode ξ, woodinSparseSourceStageCardinals ξ⟩ₖ)
    (hi : i ∈ succ (woodinSourceIndex γ)) :
    f ‘ ((forcingCodeP (woodinSparseSourceStageCode γ)) ‘ i) =
      (forcingCodeP (woodinSparseSourceStageCode ξ)) ‘ (f ‘ i) := by
  let := hierarchy_transitive (ordinalAdd γ (ω : V))
  have hs := (kpair_components_mem_transitive hcode).1
  have hp : ⟨forcingCodeP (woodinSparseSourceStageCode γ),
      kpair.π₂ (woodinSparseSourceStageCode γ)⟩ₖ ∈ hierarchy (ordinalAdd γ (ω : V)) :=
    woodinSparseSourceStageCode_pair_first γ ▸ hs
  have hcomponents := kpair_components_mem_transitive hp
  have hscap := (woodinSparseSourceStageCode_capture_components he hcode hcap).1
  have hc : f ‘ (forcingCodeP (woodinSparseSourceStageCode γ)) =
      forcingCodeP (woodinSparseSourceStageCode ξ) := by
    have hv := he.value_pair hcomponents.1 hcomponents.2 hp
    rw [← woodinSparseSourceStageCode_pair_first γ, hscap] at hv
    simpa only [forcingCodeP, kpair.π₁_kpair] using (congrArg kpair.π₁ hv).symm
  have ht := (woodinSparseSourceStageCode_valid hΩ hAC hγ).tableP
  have hD : succ (woodinSourceIndex γ) ∈ hierarchy (ordinalAdd γ (ω : V)) := by
    simpa only [woodinSourceIndex_successor] using woodinSourceIndex_successor_finiteRank γ
  have hv := he.value_apply hcomponents.1 hD ht.function ht.domain_eq hi
  rw [hc] at hv
  exact hv.symm

theorem woodinSparseSourceStageCode_restriction_mem_at_fixedPoint {Ω γ κ p : V}
    [IsOrdinal γ] [IsOrdinal κ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hγ : γ ⊆ Ω)
    (hκγ : κ ∈ γ) (hfix : (kpair.π₂ (woodinIterationRec κ)) ‘ κ = κ)
    (hp : p ∈ (forcingCodeP (woodinSparseSourceStageCode γ)) ‘ (woodinSourceIndex γ)) :
    p ↾ (succ (woodinSourceIndex κ)) ∈ hierarchy κ := by
  let := hΩ.inaccessible.1
  have hκΩ := hγ κ hκγ
  have hsubκ : κ ⊆ Ω := IsOrdinal.toIsTransitive.transitive _ hκΩ
  have hglobal : (kpair.π₂ (woodinIterationRec Ω)) ‘ κ = κ :=
    (woodinIterationRec_cardinal_eq_endpoint hΩ hAC
      (mem_succ_iff.mpr (Or.inr hκΩ))).symm.trans hfix
  rw [(woodinSparseSourceStageCode_row (mem_succ_self γ)).1] at hp
  have hγcode := woodinSparseStageCode_valid hΩ hAC hγ
  have hm := hγcode.system.split.projMaps κ (mem_succ_iff.mpr (Or.inr hκγ))
    γ (mem_succ_self γ) (IsOrdinal.toIsTransitive.transitive _ hκγ) p hp
  rw [woodinSparseStageCode_projection hΩ hAC hγ hκγ hp] at hm
  rw [← (woodinSparseStageCode_valid hΩ hAC hsubκ).tableP.value_of_subset
    hγcode.tableP (woodinSparseStageCode_extends_previous hΩ hAC hγ hκγ).subP
    (mem_succ_self κ)] at hm
  exact woodinSparseStageCode_rows_subset_at_fixedPoint hΩ hAC hκΩ hglobal κ
    (mem_succ_self κ) _ hm

theorem woodinSparseSourceStageCode_carrier_mem_of_code {A γ i : V}
    [IsTransitive A] [IsOrdinal γ]
    (hcode : woodinSparseSourceStageCode γ ∈ A)
    (hvalid : IsForcingIterationCode (succ (woodinSourceIndex γ)) (woodinSparseSourceStageCode γ))
    (hi : i ∈ succ (woodinSourceIndex γ)) :
    (forcingCodeP (woodinSparseSourceStageCode γ)) ‘ i ∈ A := by
  have hp : ⟨forcingCodeP (woodinSparseSourceStageCode γ),
      kpair.π₂ (woodinSparseSourceStageCode γ)⟩ₖ ∈ A :=
    woodinSparseSourceStageCode_pair_first γ ▸ hcode
  have hP := (kpair_components_mem_transitive hp).1
  let := hvalid.tableP.function
  exact (IsCodedMembershipEmbedding.function_argument_mem hP (hvalid.tableP.domain_eq.symm ▸ hi)).2

/-- The actual captured source conditions have the common marked prefix required
for the master-condition quotient. -/
theorem woodinSparseSourceStageCode_capture_projection
    {Ω f γ ξ κ p : V} [IsOrdinal γ] [IsOrdinal ξ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hξ : ξ ∈ Ω)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd γ (ω : V)))
      (hierarchy (ordinalAdd ξ (ω : V))) f)
    (hcode : ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ ∈
      hierarchy (ordinalAdd γ (ω : V)))
    (hcap : f ‘ ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ =
      ⟨woodinSparseSourceStageCode ξ, woodinSparseSourceStageCardinals ξ⟩ₖ)
    (himage : f ‘ γ = ξ) (hfix : (kpair.π₂ (woodinIterationRec ξ)) ‘ ξ = ξ)
    (hκ : IsCriticalPoint (hierarchy (ordinalAdd γ (ω : V))) f κ)
    (hκγ : κ ∈ γ) (hgap : γ ∈ f ‘ κ)
    (hp : p ∈ (forcingCodeP (woodinSparseSourceStageCode γ)) ‘ (woodinSourceIndex γ)) :
    f ‘ p ∈ (forcingCodeP (woodinSparseSourceStageCode ξ)) ‘ (woodinSourceIndex ξ) ∧
    ((forcingCodeπ (woodinSparseSourceStageCode ξ)) ‘
      ⟨woodinSourceIndex (f ‘ κ), woodinSourceIndex ξ⟩ₖ) ‘ (f ‘ p) =
    ((forcingCodeπ (woodinSparseSourceStageCode γ)) ‘
      ⟨woodinSourceIndex κ, woodinSourceIndex γ⟩ₖ) ‘ p := by
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
  have hγξ := IsOrdinal.toIsTransitive.mem_trans hgap hδξ
  have hγΩ := IsOrdinal.toIsTransitive.mem_trans hγξ hξ
  have hsubγ : γ ⊆ Ω := IsOrdinal.toIsTransitive.transitive _ hγΩ
  have hsubξ : ξ ⊆ Ω := IsOrdinal.toIsTransitive.transitive _ hξ
  obtain ⟨_, hκfix, _, hγinac, hκinac, hδinac, _, hfixed⟩ :=
    woodinSparseSourceStageCode_capture_marked hΩ hAC hξ he hcode hcap himage hfix hκ hκγ hgap
  have hsγ := woodinSourceIndex_infinite (fun hh ↦ mem_asymm hh hγinac.2.1)
  have hsκ := woodinSourceIndex_infinite (fun hh ↦ mem_asymm hh hκinac.2.1)
  have hsδ := woodinSourceIndex_infinite (fun hh ↦ mem_asymm hh hδinac.2.1)
  have hξinac := hfix ▸ ((woodinIterationExit hΩ hAC).2.1 ξ hξ).1.inaccessible ξ (mem_succ_self ξ)
  have hsξ := woodinSourceIndex_infinite (fun hh ↦ mem_asymm hh hξinac.2.1)
  have hPA := woodinSparseSourceStageCode_carrier_mem_of_code
    (kpair_components_mem_transitive hcode).1 (woodinSparseSourceStageCode_valid hΩ hAC hsubγ)
    (mem_succ_self (woodinSourceIndex γ))
  have hpA := (hierarchy_transitive (ordinalAdd γ (ω : V))).mem_trans hp hPA
  have hcar := woodinSparseSourceStageCode_capture_carrier hΩ hAC hsubγ he hcode hcap
    (mem_succ_self (woodinSourceIndex γ))
  have hfp : f ‘ p ∈ (forcingCodeP (woodinSparseSourceStageCode ξ)) ‘ (woodinSourceIndex ξ) := by
    have hm := (he.value_mem_iff hpA hPA).mpr hp
    rw [hcar, hsγ, himage] at hm
    simpa only [hsξ] using hm
  refine ⟨hfp, ?_⟩
  have hprefix := woodinSparseSourceStageCode_restriction_mem_at_fixedPoint hΩ hAC hsubγ hκγ hκfix hp
  rw [hsκ] at hprefix
  have hprefixFixed := hfixed _ hprefix
  have hlim : ∀ β ∈ ordinalAdd γ (ω : V), succ β ∈ ordinalAdd γ (ω : V) :=
    fun _ hh ↦ ordinalAdd_omega_succ_closed γ hh
  have hsκA : succ κ ∈ hierarchy (ordinalAdd γ (ω : V)) :=
    ordinal_subset_hierarchy _ _ (hlim _ (IsOrdinal.toIsTransitive.mem_trans hκγ (ordinalAdd_omega_gt γ)))
  have hr := limitRankEmbedding_restriction hlim he hpA hsκA
  rw [he.value_succ hκ.mem_domain hsκA, hprefixFixed] at hr
  rw [woodinSparseSourceStageCode_projection hΩ hAC hsubξ hδξ hfp,
    woodinSparseSourceStageCode_projection hΩ hAC hsubγ hκγ hp, hsδ, hsκ]
  exact hr.symm

end ZFVP
