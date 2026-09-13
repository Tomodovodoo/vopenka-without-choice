import ZFVP.ModelTheory.WoodinSourceRecursionExit
import ZFVP.ModelTheory.WoodinSourceCodeCompatibility
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Checked correspondence data for the decoded least-failure-seed presentation.
The independent manuscript audit is an external validation obligation, not a field
that may be assumed to construct this record. -/
structure WoodinSourceCorrespondenceExit (δ : V) [IsOrdinal δ]
    : Prop extends WoodinSourceRecursionExit δ where
  indexZero : woodinSourceIndex (∅ : V) = 1
  indexLeftInverse (α : V) [IsOrdinal α] : woodinRecursiveIndex (woodinSourceIndex α) = α
  indexRightInverse (β : V) [IsOrdinal β] (hβ : β ≠ ∅) :
    woodinSourceIndex (woodinRecursiveIndex β) = β
  indexOrder {α β : V} [IsOrdinal α] [IsOrdinal β] :
    woodinSourceIndex α ∈ woodinSourceIndex β ↔ α ∈ β
  indexSuccessor (α : V) [IsOrdinal α] : woodinSourceIndex (succ α) = succ (woodinSourceIndex α)
  indexLimit (θ : V) [IsOrdinal θ] (hzero : (∅ : V) ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ) :
    woodinSourceIndex θ = θ
  prefixStage (θ : V) [IsOrdinal θ] (hθ : θ ⊆ δ) {i : V} (hi : i ∈ θ) :
    woodinIterationStage (woodinSourceCode θ (woodinIterationPrefix θ))
      (woodinSourceCardinals θ (woodinIterationCardinalPrefix θ)) (woodinSourceIndex i) =
    woodinIterationStage (kpair.π₁ (woodinIterationRec i)) (kpair.π₂ (woodinIterationRec i)) i
  indexEndpoint : woodinSourceIndex δ = δ
  prefixes (θ : V) [IsOrdinal θ] (hθ : θ ⊆ δ) :
    WoodinSourceCodeCompatibility θ (woodinIterationPrefix θ) (woodinIterationCardinalPrefix θ)
  full : WoodinSourceCodeCompatibility (succ δ) (kpair.π₁ (woodinIterationRec δ))
    (kpair.π₂ (woodinIterationRec δ))
  limitCardinal (θ : V) [IsOrdinal θ] (hθ : θ ⊆ δ) (hzero : (∅ : V) ∈ θ) :
    woodinLimitCardinal (woodinSourceCardinals θ (woodinIterationCardinalPrefix θ)) =
      woodinLimitCardinal (woodinIterationCardinalPrefix θ)
  endpoint : IsCanonicalForcingTransport
    ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
    ((forcingCodeP (forcingDirectCode δ (woodinSourceCode δ (woodinIterationPrefix δ)))) ‘ δ)
    ((forcingCodeR (forcingDirectCode δ (woodinSourceCode δ (woodinIterationPrefix δ)))) ‘ δ)
    (woodinSeedThreadMap δ ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ))
  successorTransport {x y f : V}
    (hR : IsForcingPreorder (woodinStagePoset x) (woodinStageOrder x))
    (hS : IsForcingPreorder (woodinStagePoset y) (woodinStageOrder y))
    (hf : IsForcingIsomorphism (woodinStagePoset x) (woodinStageOrder x)
      (woodinStagePoset y) (woodinStageOrder y) f)
    (ht : IsForcingTop (woodinStagePoset x) (woodinStageOrder x) (woodinStageTop x))
    (ht' : IsForcingTop (woodinStagePoset y) (woodinStageOrder y) (woodinStageTop y))
    (hft : f ‘ (woodinStageTop x) = woodinStageTop y)
    (hκ : woodinStageCardinal x = woodinStageCardinal y) :
    (
    let c := woodinPrefixCutoff (woodinStagePoset x) (woodinStageOrder x)
      (woodinStageTop x) (woodinStageCardinal x)
    IsCanonicalForcingTransport (woodinStagePoset (woodinSuccessorStep x))
      (woodinStageOrder (woodinSuccessorStep x))
      (woodinStagePoset (woodinSuccessorStep y)) (woodinStageOrder (woodinSuccessorStep y))
      (twoStepIsomorphismMap (woodinStagePoset x) (woodinStageOrder x)
        (saturatedWoodinPrefixPosetName (woodinStagePoset x) (woodinStageOrder x)
          (woodinStageTop x) (woodinStageCardinal x) c) ∅ f) )

theorem woodinSourceCorrespondenceExit {δ : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V) :
    let _ := hδ.inaccessible.1
    WoodinSourceCorrespondenceExit δ := by
  let := hδ.inaccessible.1
  exact {
    toWoodinSourceRecursionExit := woodinSourceRecursionExit hδ hAC
    indexZero := woodinSourceIndex_zero
    indexLeftInverse := woodinRecursiveIndex_sourceIndex
    indexRightInverse := woodinSourceIndex_recursiveIndex
    indexOrder := woodinSourceIndex_mem_iff
    indexSuccessor := woodinSourceIndex_successor
    indexLimit := woodinSourceIndex_limit
    prefixStage := fun θ _ hθ _ hi ↦ woodinSourceCode_actual_prefix_stage (θ := θ) hδ hAC hθ hi
    indexEndpoint := woodinSourceIndex_supercompact hδ
    prefixes := fun θ _ hθ ↦ woodinSourceCode_actual_prefix_compatibility (θ := θ) hδ hAC hθ
    full := woodinSourceCode_actual_full_compatibility hδ hAC
    limitCardinal := fun θ _ hθ hzero ↦ woodinSourceCardinals_actual_prefix_limit (θ := θ) hδ hAC hθ hzero
    endpoint := (woodinSourceCode_endpoint_isomorphism hδ hAC).canonicalTransport
    successorTransport := fun hR hS hf ht ht' hft hκ ↦
      (woodinSuccessorStep_isomorphism hR hS hf ht ht' hft hκ).canonicalTransport }
end ZFVP





