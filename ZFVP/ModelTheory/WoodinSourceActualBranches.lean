import ZFVP.ModelTheory.WoodinSourceInvariant
import ZFVP.ModelTheory.WoodinSourceCompletedInverse
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSourceCode_actual_direct_stage_isomorphism {δ θ : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V)
    (hθ : θ ⊆ δ) (hzero : (∅ : V) ∈ θ) (h0 : θ ≠ ∅) (hs : θ ≠ succ (⋃ˢ θ))
    (hi : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    let actual := woodinSourceCode (succ θ) (kpair.π₁ (woodinIterationRec θ))
    let branch := forcingDirectCode (woodinSourceIndex θ) (woodinSourceCode θ (woodinIterationPrefix θ))
    IsForcingIsomorphism ((forcingCodeP actual) ‘ (woodinSourceIndex θ))
      ((forcingCodeR actual) ‘ (woodinSourceIndex θ))
      ((forcingCodeP branch) ‘ (woodinSourceIndex θ)) ((forcingCodeR branch) ‘ (woodinSourceIndex θ))
      (woodinSeedThreadMap θ ((forcingCodeP (forcingDirectCode θ (woodinIterationPrefix θ))) ‘ θ)) := by
  dsimp only
  simp only [woodinSourceCode, forcingCodeP_code, forcingCodeR_code,
    woodinInsertSeed_at_sourceIndex (mem_succ_self θ)]
  rw [woodinIterationRec_direct h0 hs hi, kpair.π₁_kpair]
  have hx := woodinIterationExit hδ hAC
  exact woodinSourceCode_direct_isomorphism
    (woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hθ i hi)).1)).code hzero

theorem woodinSourceCode_actual_inverse_stage_isomorphism {δ θ : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V)
    (hθ : θ ⊆ δ) (hzero : (∅ : V) ∈ θ) (h0 : θ ≠ ∅) (hs : θ ≠ succ (⋃ˢ θ))
    (hi : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    let actual := woodinSourceCode (succ θ) (kpair.π₁ (woodinIterationRec θ))
    let branch := woodinInverseSourceCode (woodinSourceIndex θ)
      (woodinSourceCode θ (woodinIterationPrefix θ)) (woodinSourceCardinals θ (woodinIterationCardinalPrefix θ))
    IsForcingIsomorphism ((forcingCodeP actual) ‘ (woodinSourceIndex θ))
      ((forcingCodeR actual) ‘ (woodinSourceIndex θ))
      ((forcingCodeP branch) ‘ (woodinSourceIndex θ)) ((forcingCodeR branch) ‘ (woodinSourceIndex θ))
      (woodinSourceInverseCollapseMap θ (woodinIterationPrefix θ)
        (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) := by
  dsimp only
  simp only [woodinSourceCode, forcingCodeP_code, forcingCodeR_code,
    woodinInsertSeed_at_sourceIndex (mem_succ_self θ)]
  rw [woodinIterationRec_inverse h0 hs hi, kpair.π₁_kpair]
  exact woodinSourceCode_actual_completed_inverse hδ hAC hθ hzero
theorem woodinSourceCode_actual_successor_stage (k : V) [IsOrdinal k] :
    woodinIterationStage
      (woodinSourceCode (succ (succ k)) (kpair.π₁ (woodinIterationRec (succ k))))
      (woodinSourceCardinals (succ (succ k)) (kpair.π₂ (woodinIterationRec (succ k))))
      (succ (woodinSourceIndex k)) =
    woodinSuccessorStep (woodinIterationStage
      (woodinSourceCode (succ k) (woodinIterationPrefix (succ k)))
      (woodinSourceCardinals (succ k) (woodinIterationCardinalPrefix (succ k))) (woodinSourceIndex k)) := by
  rw [woodinIterationRec_successor, kpair.π₁_kpair, kpair.π₂_kpair]
  exact woodinSourceCode_successor_stage k _ _
theorem woodinSourceCode_actual_firstRestoration :
    woodinIterationStage
      (woodinSourceCode (succ ∅) (kpair.π₁ (woodinIterationRec (∅ : V))))
      (woodinSourceCardinals (succ ∅) (kpair.π₂ (woodinIterationRec (∅ : V))))
      (woodinSourceIndex ∅) = woodinSuccessorStep (woodinSeedStage : V) := by
  rw [woodinIterationRec_initial, kpair.π₁_kpair, kpair.π₂_kpair]
  exact woodinSourceCode_firstRestoration




theorem woodinSourceCode_actual_prefix_stage {δ θ i : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (hθ : θ ⊆ δ) (hi : i ∈ θ) :
    woodinIterationStage (woodinSourceCode θ (woodinIterationPrefix θ))
      (woodinSourceCardinals θ (woodinIterationCardinalPrefix θ)) (woodinSourceIndex i) =
    woodinIterationStage (kpair.π₁ (woodinIterationRec i)) (kpair.π₂ (woodinIterationRec i)) i := by
  rw [woodinSourceCode_stage hi]
  have hx := woodinIterationExit hδ hAC
  have hh := woodinIterationHistory_of_stages (fun j hj ↦ (hx.2.1 j (hθ j hj)).1)
  change woodinIterationStage (forcingIterationCodeUnion θ (woodinHistoryCodes (woodinIterationHistory θ)))
    (woodinHistoryCardinalUnion θ (woodinHistoryCardinals (woodinIterationHistory θ))) i = _
  rw [hh.union_stage hi (mem_succ_self i), woodinIterationHistory_code_value hi,
    woodinIterationHistory_cardinal_value hi]


end ZFVP


