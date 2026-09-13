import ZFVP.ModelTheory.WoodinDirectedActualTransfer
import ZFVP.ModelTheory.WoodinSparseQuotientForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingContext.woodinSparse_quotient_directedClosedBelow_zf
    (A : ForcingContext V) {Ω θ i : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hi : i ∈ θ)
    (hP : A.P = (forcingCodeP (woodinSparseStageCode i)) ‘ i)
    (hR : A.R = (forcingCodeR (woodinSparseStageCode i)) ‘ i) (ho : A.one = ∅) :
    ∀ β ∈ A.check ((kpair.π₂ (woodinIterationRec i)) ‘ i),
      IsForcingDirectedClosedAt
        (A.projectionQuotient ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
          ((forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨i, θ⟩ₖ))
        (forcingSeparativeOrder
          (A.projectionQuotient ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
            ((forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨i, θ⟩ₖ))
          (A.projectionQuotientOrder ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
            ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ)
            ((forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨i, θ⟩ₖ))) β := by
  let := IsOrdinal.of_mem hi
  have hisub : i ⊆ Ω := fun x hx ↦ hθ x (IsOrdinal.toIsTransitive.transitive _ hi x hx)
  have hsi := woodinIterationStageCode_valid_le hΩ hAC hisub
  have hst := woodinIterationStageCode_valid_le hΩ hAC hθ
  have hci := woodinSparseStageCode_valid hΩ hAC hisub
  have hct := woodinSparseStageCode_valid hΩ hAC hθ
  have hκ : IsOrdinal ((kpair.π₂ (woodinIterationRec i)) ‘ i) := by
    let := hΩ.inaccessible.1
    have hiΩ := hθ i hi
    exact (((woodinIterationExit hΩ hAC).2.1 i hiΩ).1.inaccessible i (mem_succ_self i)).1
  let := hκ
  have hclosed : ∀ (B : ForcingContext V),
      B.P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i →
      B.R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
      B.one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i →
      ∀ α ∈ B.check ((kpair.π₂ (woodinIterationRec i)) ‘ i),
        IsForcingDirectedClosedAt
          (B.projectionQuotient ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ)
            ((forcingCodeπ (kpair.π₁ (woodinIterationRec θ))) ‘ ⟨i, θ⟩ₖ))
          (forcingSeparativeOrder
            (B.projectionQuotient ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ)
              ((forcingCodeπ (kpair.π₁ (woodinIterationRec θ))) ‘ ⟨i, θ⟩ₖ))
            (B.projectionQuotientOrder ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ)
              ((forcingCodeR (kpair.π₁ (woodinIterationRec θ))) ‘ θ)
              ((forcingCodeπ (kpair.π₁ (woodinIterationRec θ))) ‘ ⟨i, θ⟩ₖ))) α := by
    intro B hBP hBR hBo
    exact B.woodinActual_quotient_directedClosedBelow_zf hΩ hAC
      (IsOrdinal.toIsTransitive.transitive _ hi) hθ hBP hBR hBo
  obtain ⟨P, R, o, G, hRa, hoa, hG⟩ := A
  dsimp only at hP hR ho
  subst P R o
  have hh := equivalentRetraction_quotient_directedClosedBelow
    (hsi.system.order.preorder i (mem_succ_self i)) (hsi.system.tops.top i (mem_succ_self i))
    (woodinNormalizationRec_retraction_le hΩ hAC hisub)
    ((woodinNormalizedStage_through_endpoint hΩ hAC hisub).1.system.order.preorder i (mem_succ_self i))
    (woodinNormalizedStage_top_mem hΩ hAC hisub)
    (fun _ hp ↦ (woodinNormalizationRec_equivalent_le hΩ hAC hisub hp).1)
    (woodinSparseStageMap_isomorphism hΩ hAC hisub) (hci.system.order.preorder i (mem_succ_self i))
    (woodinIterationStage_projection_to_row hΩ hAC hθ hi) (hst.system.order.preorder θ (mem_succ_self θ))
    (woodinSparseStage_projection_to_row hΩ hAC hθ hi) (hct.system.order.preorder θ (mem_succ_self θ))
    (woodinSparseRealizationMap_projection hΩ hAC hθ).maps
    (woodinSparseRealizationInverse_maps hΩ hAC hθ)
    (fun _ hq ↦ woodinSparseRealizationMap_right_inverse hΩ hAC hθ hq)
    (fun _ hp _ hq ↦ (woodinSparseRealizationMap_order_iff hΩ hAC hθ hp hq).symm)
    (fun p hp ↦ ?_) hclosed G hG
  · have he := woodinSparseStageMap_raw_top hΩ hAC hisub
    let B : ForcingContext V := ⟨_, _,
      (woodinSparseStageMap i) ‘ ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i),
      G, hRa, he.symm ▸ hoa, hG⟩
    have hB : B = ⟨_, _, ∅, G, hRa, hoa, hG⟩ := by
      dsimp only [B]
      congr 1
    change ∀ β ∈ B.check ((kpair.π₂ (woodinIterationRec i)) ‘ i),
      IsForcingDirectedClosedAt
        (B.projectionQuotient ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
          ((forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨i, θ⟩ₖ))
        (forcingSeparativeOrder
          (B.projectionQuotient ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
            ((forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨i, θ⟩ₖ))
          (B.projectionQuotientOrder ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
            ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ)
            ((forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨i, θ⟩ₖ))) β at hh
    rwa [hB] at hh
  · change ((forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨i, θ⟩ₖ) ‘ ((woodinSparseRealizationMap θ) ‘ p) =
      (woodinSparseRealizationMap i) ‘ (((forcingCodeπ (kpair.π₁ (woodinIterationRec θ))) ‘ ⟨i, θ⟩ₖ) ‘ p)
    rw [woodinSparseStageCode_projection hΩ hAC hθ hi
      (function_value_mem (woodinSparseRealizationMap_projection hΩ hAC hθ).maps hp)]
    exact woodinSparseRealizationMap_restrict hΩ hAC hθ hi hp

/-- Directed bounds in the actual sparse source code, with the seed reindexing
shown explicitly. Both the bound and the cutoff are transported from construction. -/
theorem ForcingContext.woodinSparseSource_quotient_directedClosedBelow_zf
    (A : ForcingContext V) {Ω θ i : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hi : i ∈ θ)
    (hP : A.P = (forcingCodeP (woodinSparseSourceStageCode i)) ‘ (woodinSourceIndex i))
    (hR : A.R = (forcingCodeR (woodinSparseSourceStageCode i)) ‘ (woodinSourceIndex i))
    (ho : A.one = ∅) :
    ∀ β ∈ A.check ((woodinSparseSourceStageCardinals i) ‘ (woodinSourceIndex i)),
      IsForcingDirectedClosedAt
        (A.projectionQuotient ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
          ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ))
        (forcingSeparativeOrder
          (A.projectionQuotient ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
            ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ))
          (A.projectionQuotientOrder ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
            ((forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
            ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ))) β := by
  let := IsOrdinal.of_mem hi
  have hiΩ : i ⊆ Ω := subset_trans (IsOrdinal.toIsTransitive.transitive _ hi) hθ
  rw [(woodinSparseSourceStageCode_row (mem_succ_self i)).1] at hP
  rw [(woodinSparseSourceStageCode_row (mem_succ_self i)).2] at hR
  rw [woodinSparseSourceStageCardinals_value hΩ hAC hiΩ (mem_succ_self i),
    (woodinSparseSourceStageCode_row (mem_succ_self θ)).1,
    (woodinSparseSourceStageCode_row (mem_succ_self θ)).2,
    (woodinSparseSourceStageCode_matrices (mem_succ_iff.mpr (Or.inr hi)) (mem_succ_self θ)).1]
  exact A.woodinSparse_quotient_directedClosedBelow_zf hΩ hAC hθ hi hP hR ho

theorem ForcingContext.woodinSparseSource_infinite_quotient_directedClosedBelow_zf
    (A : ForcingContext V) {Ω θ i : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hi : i ∈ θ) (hio : i ∉ (ω : V))
    (hP : A.P = (forcingCodeP (woodinSparseSourceStageCode i)) ‘ i)
    (hR : A.R = (forcingCodeR (woodinSparseSourceStageCode i)) ‘ i)
    (ho : A.one = ∅) :
    ∀ β ∈ A.check ((woodinSparseSourceStageCardinals i) ‘ i),
      IsForcingDirectedClosedAt
        (A.projectionQuotient ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ θ)
          ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨i, θ⟩ₖ))
        (forcingSeparativeOrder
          (A.projectionQuotient ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ θ)
            ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨i, θ⟩ₖ))
          (A.projectionQuotientOrder ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ θ)
            ((forcingCodeR (woodinSparseSourceStageCode θ)) ‘ θ)
            ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨i, θ⟩ₖ))) β := by
  let := IsOrdinal.of_mem hi
  have hiidx := woodinSourceIndex_infinite hio
  have hθo : θ ∉ (ω : V) := fun h ↦ hio (IsOrdinal.toIsTransitive.mem_trans hi h)
  have hθidx := woodinSourceIndex_infinite hθo
  have hP' : A.P = (forcingCodeP (woodinSparseSourceStageCode i)) ‘ (woodinSourceIndex i) := by
    simpa only [hiidx] using hP
  have hR' : A.R = (forcingCodeR (woodinSparseSourceStageCode i)) ‘ (woodinSourceIndex i) := by
    simpa only [hiidx] using hR
  simpa only [hiidx, hθidx] using
    A.woodinSparseSource_quotient_directedClosedBelow_zf hΩ hAC hθ hi hP' hR' ho
end ZFVP


