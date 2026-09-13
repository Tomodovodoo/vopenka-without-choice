import ZFVP.ModelTheory.WoodinEndpointRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingContext.projectionInclusion_hierarchy_of_forced_rank (A B : ForcingContext V)
    {θ κ π E : V} [IsOrdinal θ] [IsOrdinal κ]
    (hπ : IsForcingSplitProjection A.P A.R B.P B.R π E)
    (he : forcingProjectionGeneric A.P A.R π B.G = A.G)
    (hDC : ∀ p ∈ A.P, p ∈ forcingFormula A.P A.R dependentChoiceBelowFormula
      (standardTuple ![checkName A.one κ]))
    (hc : ForcesProjectionQuotientClosedBelow A.P A.R A.one B.P B.R π κ)
    (hr : ForcesRankEnumerations A.P A.R A.one θ κ) :
    A.projectionInclusion B hπ he (hierarchy (A.check θ)) = hierarchy (B.check θ) := by
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  have hd : ∀ γ ∈ A.check κ, InternalDependentChoiceAt γ :=
    (Defined.eval_iff _).mp ((A.checked_unary_truth dependentChoiceBelowFormula κ).mpr
      ⟨p, hp, hDC p (A.generic.1.1 p hp)⟩)
  have hh := A.projectionInclusion_hierarchy_of_separative_closed B hπ he hd
    (A.projectionQuotient_closedBelow_of_forced hπ.projection B.order hc)
    (A.rankEnumerations_of_forced hr)
  rwa [A.projectionInclusion_check B hπ he] at hh

/-- Rank agreement along a coded iteration projection. The forcing contexts
are identified with the actual table entries, including the earlier top. -/
theorem IsWoodinIteration.projection_rankAgreement {δ θ s K i j π E : V}
    [IsOrdinal θ] (h : IsWoodinIteration δ θ s K)
    (hc : HasWoodinQuotientClosure θ s K) (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j)
    (hr : WoodinRankStage i s K) (A B : ForcingContext V)
    (hAP : A.P = (forcingCodeP s) ‘ i) (hAR : A.R = (forcingCodeR s) ‘ i)
    (hAt : A.one = (forcingCodet s) ‘ i)
    (hBP : B.P = (forcingCodeP s) ‘ j) (hBR : B.R = (forcingCodeR s) ‘ j)
    (hπv : π = (forcingCodeπ s) ‘ ⟨i, j⟩ₖ)
    (hπ : IsForcingSplitProjection A.P A.R B.P B.R π E)
    (he : forcingProjectionGeneric A.P A.R π B.G = A.G) :
    A.projectionInclusion B hπ he (hierarchy (A.check i)) = hierarchy (B.check i) := by
  let := IsOrdinal.of_mem hi
  let := (h.inaccessible i hi).1
  apply A.projectionInclusion_hierarchy_of_forced_rank B (κ := K ‘ i) hπ he
  · have hd := (h.stage i hi).2.2.2.2
    simpa only [woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
      woodinStageTop_code, woodinStageCardinal_code, hAP, hAR, hAt] using hd
  · simpa only [IterationQuotientClosedBelow, hAP, hAR, hAt, hBP, hBR, hπv] using
      hc i hi j hj hij
  · simpa only [WoodinRankStage, hAP, hAR, hAt] using hr

theorem woodinIteration_endpoint_projection_rankAgreement {ε i π E : V}
    (hε : IsWoodinSupercompact ε) (hAC : ¬InternalChoice V) (hi : i ∈ ε)
    (A B : ForcingContext V)
    (hAP : A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec ε))) ‘ i)
    (hAR : A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec ε))) ‘ i)
    (hAt : A.one = (forcingCodet (kpair.π₁ (woodinIterationRec ε))) ‘ i)
    (hBP : B.P = (forcingCodeP (kpair.π₁ (woodinIterationRec ε))) ‘ ε)
    (hBR : B.R = (forcingCodeR (kpair.π₁ (woodinIterationRec ε))) ‘ ε)
    (hπv : π = (forcingCodeπ (kpair.π₁ (woodinIterationRec ε))) ‘ ⟨i, ε⟩ₖ)
    (hπ : IsForcingSplitProjection A.P A.R B.P B.R π E)
    (he : forcingProjectionGeneric A.P A.R π B.G = A.G) :
    A.projectionInclusion B hπ he (hierarchy (A.check i)) = hierarchy (B.check i) := by
  let := hε.inaccessible.1
  have hv := woodinIteration_endpoint_valid hε hAC
  have hs : ∀ k ∈ ε, IsWoodinIteration (succ ε) (succ k)
      (kpair.π₁ (woodinIterationRec k)) (kpair.π₂ (woodinIterationRec k)) := by
    intro k hk
    exact ((woodinIterationExit hε hAC).2.1 k hk).1.enlarge_bound
      (fun _ hx ↦ mem_succ_iff.mpr (Or.inr hx))
  have hr := (woodinIterationRec_rankStage_previous hs hv.1 hi).mp
    (woodinIteration_rankStages hε i hi)
  exact hv.1.projection_rankAgreement hv.2 (mem_succ_iff.mpr (Or.inr hi))
    (mem_succ_self ε) (IsOrdinal.toIsTransitive.transitive _ hi) hr A B
    hAP hAR hAt hBP hBR hπv hπ he

end ZFVP
