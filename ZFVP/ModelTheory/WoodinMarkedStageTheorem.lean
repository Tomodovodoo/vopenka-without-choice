import ZFVP.ModelTheory.WoodinSparseSourceFactorization
import ZFVP.ModelTheory.WoodinDirectedSourceTransfer
import ZFVP.ModelTheory.WoodinFixedPointRankQuotient
import ZFVP.ModelTheory.WoodinSparseEndpointZFC

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The source tail is an actual internal forcing. Directed closure is stated
on its separative preorder, as in the closure construction; homogeneity uses
actual automorphisms of its original order. Neither property is a premise. -/
def HasWoodinSourceTails (Ω : V) : Prop :=
  ∀ (θ : V) [IsOrdinal θ], θ ⊆ Ω →
    ∀ j ∈ succ (woodinSourceIndex θ), ∀ A : ForcingContext V,
      A.P = (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ j →
      A.R = (forcingCodeR (woodinSparseSourceStageCode θ)) ‘ j → A.one = ∅ →
      let Q := A.projectionQuotient
        ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
        ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨j,woodinSourceIndex θ⟩ₖ)
      let R := A.projectionQuotientOrder
        ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
        ((forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
        ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨j,woodinSourceIndex θ⟩ₖ)
      (∀ α ∈ A.check ((woodinSparseSourceStageCardinals θ) ‘ j),
        IsForcingDirectedClosedAt Q (forcingSeparativeOrder Q R) α) ∧
      (∀ p ∈ Q, ∀ q ∈ Q, ∃ f, IsForcingAutomorphism Q R f ∧ ForcingCompatible Q R (f ‘ p) q)

structure WoodinMarkedStageConclusion {Ω : V} (hΩ : IsWoodinSupercompact Ω)
    (hAC : ¬InternalChoice V) : Prop where
  construction : WoodinIterationExit Ω
  sourceCode : ∀ (θ : V) [IsOrdinal θ], θ ⊆ Ω →
    IsForcingIterationCode (succ (woodinSourceIndex θ)) (woodinSparseSourceStageCode θ)
  marked : ∀ γ ∈ succ Ω, IsWoodinSupercompact γ → (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ
  factorization : ∀ (θ : V) [IsOrdinal θ], θ ⊆ Ω →
    ∀ j ∈ succ (woodinSourceIndex θ), ∀ A B : ForcingContext V,
      A.P = (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ j →
      A.R = (forcingCodeR (woodinSparseSourceStageCode θ)) ‘ j →
      B.P = (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ) →
      B.R = (forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ) →
      let π := (forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨j,woodinSourceIndex θ⟩ₖ
      let e := (forcingCodeE (woodinSparseSourceStageCode θ)) ‘ ⟨j,woodinSourceIndex θ⟩ₖ
      ∃ hs : IsForcingSplitProjection A.P A.R B.P B.R π e,
        ∀ hG : forcingProjectionGeneric A.P A.R π B.G = A.G,
          ∃ F : (A.projectionQuotientContext B hs hG).Model ≃ B.Model,
            (∀ x y, F x ∈ F y ↔ x ∈ y) ∧
            ∀ x : V, F ((A.projectionQuotientContext B hs hG).check (A.check x)) = B.check x
  tails : HasWoodinSourceTails Ω
  homogeneity : ∀ (θ : V) [IsOrdinal θ], θ ⊆ Ω →
    ∀ p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ,
      ∀ q ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ,
        ∃ f, IsForcingAutomorphism ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
          ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) f ∧
          ForcingCompatible ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
            ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) (f ‘ p) q
  rankAgreement : ∀ {G : Set V} (hG : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G),
    ∀ γ (hγ : γ ∈ Ω) (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ),
      ∃ F : WoodinEndpointModel.FixedPointLowNameQuotient hΩ hAC hG hγ hfix ≃
          SetDomain (hierarchy ((WoodinEndpointModel.context hΩ hAC hG).check γ)),
        ∀ x y, F x ∈ F y ↔ x ∈ y
  endpointRankAgreement : ∀ {G : Set V} (hG : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G),
    ∀ x : (WoodinEndpointModel.context hΩ hAC hG).Model,
      x ∈ hierarchy ((WoodinEndpointModel.context hΩ hAC hG).check Ω) ↔
        ∃ τ : ForcingName (woodinStageCarrier Ω), τ.val ∈ hierarchy Ω ∧
          x = WoodinEndpointModel.localNameValue hΩ hAC hG τ
  endpointZFC : ∀ {G : Set V} (hG : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G),
    (WoodinEndpointModel.RankModel hΩ hAC hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖

theorem woodinMarkedStageConclusion {Ω : V} (hΩ : IsWoodinSupercompact Ω)
    (hAC : ¬InternalChoice V) : WoodinMarkedStageConclusion hΩ hAC := by
  let := hΩ.inaccessible.1
  constructor
  · exact woodinIterationExit hΩ hAC
  · intro θ _ hθ
    exact woodinSparseSourceStageCode_valid hΩ hAC hθ
  · intro γ hγ hγSC
    let := hγSC.inaccessible.1
    exact (woodinIterationRec_cardinal_eq_endpoint hΩ hAC hγ).symm.trans
      (woodinIteration_endpoint_cardinal hγSC hAC)
  · intro θ _ hθ j hj A B hAP hAR hBP hBR
    let hs := A.woodinSparseSource_split B hΩ hAC hθ hj hAP hAR hBP hBR
    refine ⟨hs, ?_⟩
    intro hG
    exact A.woodinSparseSource_factorization B hΩ hAC hθ hj hAP hAR hBP hBR hG
  · intro θ _ hθ j hj A hP hR ho
    exact ⟨A.woodinSparseSource_all_quotient_directedClosedBelow_zf hΩ hAC hθ hj hP hR ho,
      A.woodinSparseSource_all_quotient_weak_homogeneous hΩ hAC hθ hj hP hR⟩
  · intro θ _ hθ p hp q hq
    exact woodinSparseStage_weak_homogeneous_below hΩ hAC hθ hp hq
  · intro G hG γ hγ hfix
    exact ⟨WoodinEndpointModel.fixedPointLowNameRankEquiv hΩ hAC hG hγ hfix,
      WoodinEndpointModel.fixedPointLowNameRankEquiv_mem_iff hΩ hAC hG hγ hfix⟩
  · intro G hG
    exact WoodinEndpointModel.mem_rank_iff_localName hΩ hAC hG
  · intro G hG
    exact WoodinEndpointModel.rankModel_models_zfc hΩ hAC hG

end ZFVP
