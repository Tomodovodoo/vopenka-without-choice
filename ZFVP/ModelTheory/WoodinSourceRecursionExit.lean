import ZFVP.ModelTheory.WoodinSourceActualBranches
import ZFVP.ModelTheory.WoodinSourceRawInverseDC

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The recursion equations and stage/quotient exit of the decoded source presentation.
The complete manuscript correspondence additionally requires the explicit map,
name, support and generic compatibility contract. -/
structure WoodinSourceRecursionExit (δ : V) : Prop where
  invariant : WoodinSourceInvariantExit δ
  firstRestoration :
    woodinIterationStage
      (woodinSourceCode (succ ∅) (kpair.π₁ (woodinIterationRec (∅ : V))))
      (woodinSourceCardinals (succ ∅) (kpair.π₂ (woodinIterationRec (∅ : V))))
      (woodinSourceIndex ∅) = woodinSuccessorStep (woodinSeedStage : V)
  successor (k : V) [IsOrdinal k] :
    woodinIterationStage
      (woodinSourceCode (succ (succ k)) (kpair.π₁ (woodinIterationRec (succ k))))
      (woodinSourceCardinals (succ (succ k)) (kpair.π₂ (woodinIterationRec (succ k))))
      (succ (woodinSourceIndex k)) =
    woodinSuccessorStep (woodinIterationStage
      (woodinSourceCode (succ k) (woodinIterationPrefix (succ k)))
      (woodinSourceCardinals (succ k) (woodinIterationCardinalPrefix (succ k))) (woodinSourceIndex k))
  direct (θ : V) [IsOrdinal θ] (hθ : θ ⊆ δ)
      (hzero : (∅ : V) ∈ θ) (h0 : θ ≠ ∅) (hs : θ ≠ succ (⋃ˢ θ))
      (hi : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    let actual := woodinSourceCode (succ θ) (kpair.π₁ (woodinIterationRec θ))
    let branch := forcingDirectCode (woodinSourceIndex θ) (woodinSourceCode θ (woodinIterationPrefix θ))
    IsForcingIsomorphism ((forcingCodeP actual) ‘ (woodinSourceIndex θ))
      ((forcingCodeR actual) ‘ (woodinSourceIndex θ))
      ((forcingCodeP branch) ‘ (woodinSourceIndex θ)) ((forcingCodeR branch) ‘ (woodinSourceIndex θ))
      (woodinSeedThreadMap θ ((forcingCodeP (forcingDirectCode θ (woodinIterationPrefix θ))) ‘ θ))
  inverse (θ : V) [IsOrdinal θ] (hθ : θ ⊆ δ)
      (hzero : (∅ : V) ∈ θ) (h0 : θ ≠ ∅) (hs : θ ≠ succ (⋃ˢ θ))
      (hi : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    let actual := woodinSourceCode (succ θ) (kpair.π₁ (woodinIterationRec θ))
    let branch := woodinInverseSourceCode (woodinSourceIndex θ)
      (woodinSourceCode θ (woodinIterationPrefix θ)) (woodinSourceCardinals θ (woodinIterationCardinalPrefix θ))
    IsForcingIsomorphism ((forcingCodeP actual) ‘ (woodinSourceIndex θ))
      ((forcingCodeR actual) ‘ (woodinSourceIndex θ))
      ((forcingCodeP branch) ‘ (woodinSourceIndex θ)) ((forcingCodeR branch) ‘ (woodinSourceIndex θ))
      (woodinSourceInverseCollapseMap θ (woodinIterationPrefix θ)
        (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
  rawDC (θ : V) (hθ : θ ∈ δ) (hzero : θ ≠ ∅)
      (hlim : ∀ i ∈ θ, succ i ∈ θ)
      (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    WoodinSourceRawInverseDC θ

theorem woodinSourceRecursionExit {δ : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V) : WoodinSourceRecursionExit δ where
  invariant := woodinSourceInvariantExit hδ hAC
  firstRestoration := woodinSourceCode_actual_firstRestoration
  successor := woodinSourceCode_actual_successor_stage
  direct θ _ hθ hzero h0 hs hi :=
    woodinSourceCode_actual_direct_stage_isomorphism (θ := θ) hδ hAC hθ hzero h0 hs hi
  inverse θ _ hθ hzero h0 hs hi :=
    woodinSourceCode_actual_inverse_stage_isomorphism (θ := θ) hδ hAC hθ hzero h0 hs hi
  rawDC θ hθ hzero hlim hn := woodinSourceRawInverseDC (θ := θ) hδ hAC hθ hzero hlim hn
end ZFVP

