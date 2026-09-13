import ZFVP.ModelTheory.WoodinSparseCapturedOrder

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseSourceStageCode_capture_fixed_conditions
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
    (hp : p ∈ (forcingCodeP (woodinSparseSourceStageCode κ)) ‘ (woodinSourceIndex κ)) :
    f ‘ p = p := by
  let := hΩ.inaccessible.1
  let := hκ.ordinal
  let := hierarchy_transitive (ordinalAdd γ (ω : V))
  let := hierarchy_transitive (ordinalAdd ξ (ω : V))
  let := he.value_ordinal hκ.ordinal hκ.mem_domain
  have hδξ : f ‘ κ ∈ ξ := by
    rw [← himage]
    exact (he.value_mem_iff hκ.mem_domain (ordinal_subset_hierarchy _ _ (ordinalAdd_omega_gt γ))).mpr hκγ
  have hκΩ := IsOrdinal.toIsTransitive.mem_trans hκγ
    (IsOrdinal.toIsTransitive.mem_trans hgap (IsOrdinal.toIsTransitive.mem_trans hδξ hξ))
  obtain ⟨_, hκfix, _, _, _, _, _, hfixed⟩ :=
    woodinSparseSourceStageCode_capture_marked hΩ hAC hξ he hcode hcap himage hfix hκ hκγ hgap
  have hglobal : (kpair.π₂ (woodinIterationRec Ω)) ‘ κ = κ :=
    (woodinIterationRec_cardinal_eq_endpoint hΩ hAC
      (mem_succ_iff.mpr (Or.inr hκΩ))).symm.trans hκfix
  exact hfixed p (woodinSparseSourceStageCode_rows_subset_at_fixedPoint hΩ hAC hκΩ hglobal
    (woodinSourceIndex κ) (mem_succ_self _) p hp)

/-- The actual image family is nonempty, directed by the target order, and has
the original critical prefix. No target generic or master condition is assumed. -/
theorem woodinSparseSourceStageCode_capture_filter_image
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
    (hκγ : κ ∈ γ) (hgap : γ ∈ f ‘ κ)
    {G : Set V} (hG : IsExternalForcingFilter
      ((forcingCodeP (woodinSparseSourceStageCode γ)) ‘ (woodinSourceIndex γ))
      ((forcingCodeR (woodinSparseSourceStageCode γ)) ‘ (woodinSourceIndex γ)) G) :
    let I := (fun p ↦ f ‘ p) '' G
    I.Nonempty ∧
    (∀ p ∈ I, p ∈ (forcingCodeP (woodinSparseSourceStageCode ξ)) ‘ (woodinSourceIndex ξ)) ∧
    (∀ p ∈ I, ∀ q ∈ I, ∃ r ∈ I,
      ⟨r, p⟩ₖ ∈ (forcingCodeR (woodinSparseSourceStageCode ξ)) ‘ (woodinSourceIndex ξ) ∧
      ⟨r, q⟩ₖ ∈ (forcingCodeR (woodinSparseSourceStageCode ξ)) ‘ (woodinSourceIndex ξ)) ∧
    (∀ p ∈ I, ((forcingCodeπ (woodinSparseSourceStageCode ξ)) ‘
      ⟨woodinSourceIndex (f ‘ κ), woodinSourceIndex ξ⟩ₖ) ‘ p ∈
      forcingProjectionGeneric
        ((forcingCodeP (woodinSparseSourceStageCode γ)) ‘ (woodinSourceIndex κ))
        ((forcingCodeR (woodinSparseSourceStageCode γ)) ‘ (woodinSourceIndex κ))
        ((forcingCodeπ (woodinSparseSourceStageCode γ)) ‘
          ⟨woodinSourceIndex κ, woodinSourceIndex γ⟩ₖ) G) := by
  let := hΩ.inaccessible.1
  let := hκ.ordinal
  let := hierarchy_transitive (ordinalAdd γ (ω : V))
  let := hierarchy_transitive (ordinalAdd ξ (ω : V))
  let := he.value_ordinal hκ.ordinal hκ.mem_domain
  have hδξ : f ‘ κ ∈ ξ := by
    rw [← himage]
    exact (he.value_mem_iff hκ.mem_domain (ordinal_subset_hierarchy _ _ (ordinalAdd_omega_gt γ))).mpr hκγ
  have hγΩ := IsOrdinal.toIsTransitive.mem_trans hgap (IsOrdinal.toIsTransitive.mem_trans hδξ hξ)
  have hsubγ : γ ⊆ Ω := IsOrdinal.toIsTransitive.transitive _ hγΩ
  obtain ⟨_, _, _, hγinac, _, _, _, _⟩ :=
    woodinSparseSourceStageCode_capture_marked hΩ hAC hξ he hcode hcap himage hfix hκ hκγ hgap
  have hξinac := hfix ▸ ((woodinIterationExit hΩ hAC).2.1 ξ hξ).1.inaccessible ξ (mem_succ_self ξ)
  have hγinf : γ ∉ (ω : V) := fun hh ↦ mem_asymm hh hγinac.2.1
  have hξinf : ξ ∉ (ω : V) := fun hh ↦ mem_asymm hh hξinac.2.1
  have hproj := fun p hp ↦ woodinSparseSourceStageCode_capture_projection hΩ hAC hξ he hcode hcap
    himage hfix hκ hκγ hgap (hG.1 p hp)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := hG.2.1
    exact ⟨f ‘ p, ⟨p, hp, rfl⟩⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact (hproj p hp).1
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨r, hr, hrp, hrq⟩ := hG.2.2.2 p hp q hq
    exact ⟨f ‘ r, ⟨r, hr, rfl⟩,
      woodinSparseSourceStageCode_capture_order_relation hΩ hAC hsubγ he hcode hcap hγinf hξinf himage hrp,
      woodinSparseSourceStageCode_capture_order_relation hΩ hAC hsubγ he hcode hcap hγinf hξinf himage hrq⟩
  · rintro _ ⟨p, hp, rfl⟩
    rw [(hproj p hp).2]
    have hc := woodinSparseSourceStageCode_valid hΩ hAC hsubγ
    have hlt : woodinSourceIndex κ ∈ woodinSourceIndex γ := woodinSourceIndex_mem_iff.mpr hκγ
    have hi := mem_succ_iff.mpr (Or.inr hlt)
    have hm := hc.system.split.projMaps _ hi _ (mem_succ_self _)
      (IsOrdinal.toIsTransitive.transitive _ hlt) p (hG.1 p hp)
    exact ⟨hm, p, hp, (hc.system.order.preorder _ hi).2.1 _ hm⟩

end ZFVP
