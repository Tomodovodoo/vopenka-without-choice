import ZFVP.ModelTheory.WoodinSparseSourceSubgeneric
import ZFVP.ModelTheory.WoodinSparseRankEnumerations
import ZFVP.ModelTheory.ProjectedGenericImageMaster
import ZFVP.ModelTheory.WoodinDirectedSparseTransfer
import ZFVP.ModelTheory.WoodinSparseExactRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The master condition for the actual captured image in the intermediate
marked-prefix extension. Directed closure, short enumeration, and membership
of the image family in this quotient are all derived from the construction. -/
theorem ForcingContext.woodinSparseSource_capture_master
    (A : ForcingContext V) {Ω f γ ξ κ δ : V} [IsOrdinal γ] [IsOrdinal ξ] [IsOrdinal δ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hξ : ξ ∈ Ω)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd γ (ω : V)))
      (hierarchy (ordinalAdd ξ (ω : V))) f)
    (hcode : ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ ∈
      hierarchy (ordinalAdd γ (ω : V)))
    (hcap : f ‘ ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ =
      ⟨woodinSparseSourceStageCode ξ, woodinSparseSourceStageCardinals ξ⟩ₖ)
    (himage : f ‘ γ = ξ) (hfix : (kpair.π₂ (woodinIterationRec ξ)) ‘ ξ = ξ)
    (hκ : IsCriticalPoint (hierarchy (ordinalAdd γ (ω : V))) f κ)
    (hκγ : κ ∈ γ) (hgap : γ ∈ δ) (hδ : f ‘ κ = δ)
    (hP : A.P = (forcingCodeP (woodinSparseSourceStageCode δ)) ‘ (woodinSourceIndex δ))
    (hR : A.R = (forcingCodeR (woodinSparseSourceStageCode δ)) ‘ (woodinSourceIndex δ))
    (ho : A.one = ∅) :
    ∃ t ∈ (forcingCodeP (woodinSparseSourceStageCode ξ)) ‘ (woodinSourceIndex ξ),
      ((forcingCodeπ (woodinSparseSourceStageCode ξ)) ‘ ⟨woodinSourceIndex δ, woodinSourceIndex ξ⟩ₖ) ‘ t ∈ A.G ∧
      ∀ p ∈ forcingProjectionGeneric
        ((forcingCodeP (woodinSparseSourceStageCode γ)) ‘ (woodinSourceIndex γ))
        ((forcingCodeR (woodinSparseSourceStageCode γ)) ‘ (woodinSourceIndex γ))
        ((forcingCodeπ (woodinSparseSourceStageCode δ)) ‘ ⟨woodinSourceIndex γ, woodinSourceIndex δ⟩ₖ) A.G,
        ⟨A.check t, A.check (f ‘ p)⟩ₖ ∈ forcingSeparativeOrder
          (A.projectionQuotient
            ((forcingCodeP (woodinSparseSourceStageCode ξ)) ‘ (woodinSourceIndex ξ))
            ((forcingCodeπ (woodinSparseSourceStageCode ξ)) ‘ ⟨woodinSourceIndex δ, woodinSourceIndex ξ⟩ₖ))
          (A.projectionQuotientOrder
            ((forcingCodeP (woodinSparseSourceStageCode ξ)) ‘ (woodinSourceIndex ξ))
            ((forcingCodeR (woodinSparseSourceStageCode ξ)) ‘ (woodinSourceIndex ξ))
            ((forcingCodeπ (woodinSparseSourceStageCode ξ)) ‘ ⟨woodinSourceIndex δ, woodinSourceIndex ξ⟩ₖ)) := by
  let := hΩ.inaccessible.1
  let := hκ.ordinal
  let := hierarchy_transitive (ordinalAdd γ (ω : V))
  let := hierarchy_transitive (ordinalAdd ξ (ω : V))
  have hδξ : δ ∈ ξ := by
    rw [← hδ, ← himage]
    exact (he.value_mem_iff hκ.mem_domain (ordinal_subset_hierarchy _ _ (ordinalAdd_omega_gt γ))).mpr hκγ
  have hδΩ := IsOrdinal.toIsTransitive.mem_trans hδξ hξ
  have hγΩ := IsOrdinal.toIsTransitive.mem_trans hgap hδΩ
  have hsubδ : δ ⊆ Ω := IsOrdinal.toIsTransitive.transitive _ hδΩ
  have hsubγ : γ ⊆ Ω := IsOrdinal.toIsTransitive.transitive _ hγΩ
  have hsubξ : ξ ⊆ Ω := IsOrdinal.toIsTransitive.transitive _ hξ
  obtain ⟨hγfix, _, hδfix, hγinac, _, _, _, _⟩ :=
    woodinSparseSourceStageCode_capture_marked hΩ hAC hξ he hcode hcap himage hfix hκ hκγ (hδ.symm ▸ hgap)
  rw [hδ] at hδfix
  let C := A.woodinSparseSourcePrefixContext hΩ hAC hsubδ hgap hP hR
  have hs := A.woodinSparseSourcePrefixContext_split hΩ hAC hsubδ hgap hP hR
  have hsmall : rank C.P ⊆ γ := by
    change rank ((forcingCodeP (woodinSparseSourceStageCode γ)) ‘ (woodinSourceIndex γ)) ⊆ γ
    rw [(woodinSparseSourceStageCode_row (mem_succ_self γ)).1,
      woodinSparseStageCode_rank_eq hΩ hAC hsubγ, hγfix]
  have henum := A.woodinSparseSource_rankEnumerations hΩ hAC hδΩ hP hR ho
  rw [hδfix] at henum
  have hclosed := A.woodinSparseSource_quotient_directedClosedBelow_zf hΩ hAC hsubξ hδξ hP hR ho
  rw [woodinSparseSourceStageCardinals_value hΩ hAC hsubδ (mem_succ_self δ), hδfix] at hclosed
  have hQπ := (woodinSparseSourceStage_splitProjection_to_row hΩ hAC hsubξ hδξ).projection.maps
  rw [← hP] at hQπ
  have hS := (woodinSparseSourceStageCode_valid hΩ hAC hsubξ).system.order.preorder
    (woodinSourceIndex ξ) (mem_succ_self _)
  have hAfilter : IsExternalForcingFilter
      ((forcingCodeP (woodinSparseSourceStageCode δ)) ‘ (woodinSourceIndex δ))
      ((forcingCodeR (woodinSparseSourceStageCode δ)) ‘ (woodinSourceIndex δ)) A.G := by
    simpa only [hP, hR] using A.generic.1
  have hCsub : C.G ⊆ A.G := woodinSparseSourceStage_projectedFilter_subset hΩ hAC hsubδ hgap hAfilter
  have hξinac := hfix ▸ ((woodinIterationExit hΩ hAC).2.1 ξ hξ).1.inaccessible ξ (mem_succ_self ξ)
  have hγinf : γ ∉ (ω : V) := fun hh ↦ mem_asymm hh hγinac.2.1
  have hξinf : ξ ∉ (ω : V) := fun hh ↦ mem_asymm hh hξinac.2.1
  apply C.projectedGeneric_image_master A hs rfl hsmall hgap henum hS hQπ ?_ ?_ hclosed
  · intro p hp
    have hm := woodinSparseSourceStageCode_capture_projection hΩ hAC hξ he hcode hcap
      himage hfix hκ hκγ (hδ.symm ▸ hgap) (C.generic.1.1 p hp)
    rw [hδ] at hm
    refine ⟨hm.1, ?_⟩
    rw [hm.2]
    exact hCsub (woodinSparseSourceStage_projection_mem_filter hΩ hAC hsubγ hκγ C.generic.1 hp)
  · intro p hp q hq
    obtain ⟨r, hr, hrp, hrq⟩ := C.generic.1.2.2.2 p hp q hq
    exact ⟨r, hr,
      woodinSparseSourceStageCode_capture_order_relation hΩ hAC hsubγ he hcode hcap hγinf hξinf himage hrp,
      woodinSparseSourceStageCode_capture_order_relation hΩ hAC hsubγ he hcode hcap hγinf hξinf himage hrq⟩

end ZFVP
