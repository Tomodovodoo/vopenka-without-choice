import ZFVP.ModelTheory.WoodinCanonicalBoundInverseClosureDecided
import ZFVP.ModelTheory.WoodinCanonicalBoundInverseStepDecided
import ZFVP.ModelTheory.WoodinStageInduction

/-! The outer transfinite induction over the ambient stage index.

`woodinInverse_raw_quotient_closedBelow_decided` proves closure of the raw inverse quotient at
an ambient index `θ` from two premises: `hinv`, the inverse case of the canonical bound
induction at `θ`, and `hraw`, the decided thread comparison at `θ`.
`woodinQuotientBoundAt_inverse_normalized_decided` proves `hinv` at a coordinate `j` from the
closure statement at `j` and its own decided comparison premise. Running these two against each
other by transfinite induction on the ambient index closes the loop and produces the `hinverse`
hypothesis of `woodinIteration_stages_of_inverse_closure`.

The two comparison premises quantify over `ForcingName` and `Set V`, so they are not first-order
statements about the ambient index and cannot sit inside the induction predicate. They are
carried outside it: the induction runs on the closure statement alone and the comparisons are
assumed for every ordinal below the ambient index from the start. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The `hraw` premise of `woodinInverse_raw_quotient_closedBelow_decided` at ambient index `ξ`
and coordinate `i`, written as a predicate so that it can be assumed for every `ξ` at once. -/
def WoodinInverseRawComparison (ξ i : V) : Prop :=
  ∀ p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i,
  ∀ f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i),
  ∀ α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i,
  ForcesWoodinQuotientSequence ξ i p f.val α →
  ∀ d ∈ forcingInverseCodePoset ξ (woodinIterationPrefix ξ),
  ∀ e ∈ (forcingCodeP (woodinIterationPrefix ξ)) ‘ i,
    ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix ξ)) ‘ i →
    (∀ j ∈ ξ, ∀ (G' : Set V) (hG' : IsExternalForcingGeneric
        ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G')
      (hR : IsForcingPreorder ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i))
      (ho : IsForcingTop ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
        ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)), e ∈ G' →
      let A : ForcingContext V := ⟨_, _, _, G', hR, ho, hG'⟩
      let μ : ForcingName A.P := ⟨woodinBoundCoordinateName ξ i f.val j,
        woodinBoundCoordinateName_isName ξ i f.val j⟩
      ∃ X b : A.Model,
        A.ofName μ ∈ A.check ((forcingCodeP (woodinIterationPrefix ξ)) ‘ j) ^ X ∧
          b ∈ X ∧ (A.ofName μ) ‘ b = A.check (d ‘ j)) →
    (∀ j ∈ ξ, ∀ (G' : Set V) (hG' : IsExternalForcingGeneric
        ((forcingCodeP (woodinIterationPrefix ξ)) ‘ i)
        ((forcingCodeR (woodinIterationPrefix ξ)) ‘ i) G'), e ∈ G' →
      ∀ (hRi : IsForcingPreorder ((forcingCodeP (woodinIterationPrefix ξ)) ‘ i)
          ((forcingCodeR (woodinIterationPrefix ξ)) ‘ i))
        (hti : IsForcingTop ((forcingCodeP (woodinIterationPrefix ξ)) ‘ i)
          ((forcingCodeR (woodinIterationPrefix ξ)) ‘ i)
          ((forcingCodet (woodinIterationPrefix ξ)) ‘ i))
        (μ : ForcingName ((forcingCodeP (woodinIterationPrefix ξ)) ‘ i)),
        μ.val = woodinBoundCoordinateName ξ i f.val j →
        let A : ForcingContext V := ⟨_, _, _, G', hRi, hti, hG'⟩
        ∃ X b : A.Model, A.ofName μ ∈
            A.check ((forcingCodeP (woodinIterationPrefix ξ)) ‘ j) ^ X ∧
          b ∈ X ∧ (A.ofName μ) ‘ b = A.check (d ‘ j)) →
    ∀ r ∈ forcingInverseCodePoset ξ (woodinIterationPrefix ξ),
      ⟨r, woodinQuotientBoundHistory ξ i p f.val ξ⟩ₖ
        ∈ forcingInverseCodeOrder ξ (woodinIterationPrefix ξ) →
      ∀ b ∈ (forcingCodeP (woodinIterationPrefix ξ)) ‘ i,
        ⟨b, (forcingThreadCoordinate (forcingInverseCodePoset ξ (woodinIterationPrefix ξ)) i) ‘ r⟩ₖ
          ∈ (forcingCodeR (woodinIterationPrefix ξ)) ‘ i →
        ⟨b, e⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix ξ)) ‘ i →
        ⟨(woodinInverseCodeLift ξ (woodinIterationPrefix ξ) i) ‘ ⟨r, b⟩ₖ, d⟩ₖ
          ∈ forcingInverseCodeOrder ξ (woodinIterationPrefix ξ)

/-- The `hraw` premise of `woodinQuotientBoundAt_inverse_normalized_decided` at ambient index
`ξ`, inverse-limit coordinate `j`, base coordinate `i`, condition `p` and name value `fv`. -/
def WoodinInverseStepRawComparison (ξ j i p fv : V) : Prop :=
  ∀ d ∈ forcingInverseCodePoset j (woodinIterationPrefix j),
  ∀ e ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i,
    ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
    (∀ m ∈ j, ∀ (G' : Set V) (hG' : IsExternalForcingGeneric
        ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G')
      (hR : IsForcingPreorder ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i))
      (ho : IsForcingTop ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
        ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
        ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)), e ∈ G' →
      let A : ForcingContext V := ⟨_, _, _, G', hR, ho, hG'⟩
      let μ : ForcingName A.P := ⟨woodinBoundCoordinateName ξ i fv m,
        woodinBoundCoordinateName_isName ξ i fv m⟩
      ∃ X b : A.Model,
        A.ofName μ ∈ A.check ((forcingCodeP (woodinIterationPrefix ξ)) ‘ m) ^ X ∧
          b ∈ X ∧ (A.ofName μ) ‘ b = A.check (d ‘ m)) →
    (∀ m ∈ j, ∀ (G' : Set V) (hG' : IsExternalForcingGeneric
        ((forcingCodeP (woodinIterationPrefix ξ)) ‘ i)
        ((forcingCodeR (woodinIterationPrefix ξ)) ‘ i) G'), e ∈ G' →
      ∀ (hRi : IsForcingPreorder ((forcingCodeP (woodinIterationPrefix ξ)) ‘ i)
          ((forcingCodeR (woodinIterationPrefix ξ)) ‘ i))
        (hti : IsForcingTop ((forcingCodeP (woodinIterationPrefix ξ)) ‘ i)
          ((forcingCodeR (woodinIterationPrefix ξ)) ‘ i)
          ((forcingCodet (woodinIterationPrefix ξ)) ‘ i))
        (μ : ForcingName ((forcingCodeP (woodinIterationPrefix ξ)) ‘ i)),
        μ.val = woodinBoundCoordinateName ξ i fv m →
        let A : ForcingContext V := ⟨_, _, _, G', hRi, hti, hG'⟩
        ∃ X b : A.Model, A.ofName μ ∈
            A.check ((forcingCodeP (woodinIterationPrefix ξ)) ‘ m) ^ X ∧
          b ∈ X ∧ (A.ofName μ) ‘ b = A.check (d ‘ m)) →
    ∀ r ∈ forcingInverseCodePoset j (woodinIterationPrefix j),
      ⟨r, woodinQuotientBoundHistory ξ i p fv j⟩ₖ ∈
        forcingInverseCodeOrder j (woodinIterationPrefix j) →
      ∀ b ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i,
        ⟨b, (forcingThreadCoordinate
          (forcingInverseCodePoset j (woodinIterationPrefix j)) i) ‘ r⟩ₖ ∈
          (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
        ⟨b, e⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
        ⟨(woodinInverseCodeLift j (woodinIterationPrefix j) i) ‘ ⟨r, b⟩ₖ, d⟩ₖ ∈
          forcingInverseCodeOrder j (woodinIterationPrefix j)

/-- Closure of the raw inverse quotient at every coordinate of the ambient index `θ`, by
transfinite induction on `θ`.

At `θ` the closure comes from `woodinInverse_raw_quotient_closedBelow_decided`, whose inverse
case is `woodinQuotientBoundAt_inverse_normalized_decided` at the coordinate `j`, and the
closure hypothesis of that step at `j` is the induction hypothesis. The two decided comparison
premises are assumed for every ordinal contained in `θ`. -/
theorem woodinInverse_raw_closure_of_stages [Countable V] {δ θ : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hc : ∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (h0 : ∅ ∈ θ)
    (hraw : ∀ ξ : V, ξ ⊆ θ → ∀ i ∈ ξ, WoodinInverseRawComparison ξ i)
    (hrawStep : ∀ ξ : V, ξ ⊆ θ → ∀ j ∈ ξ, ∀ i ∈ j, ∀ p : V,
      ∀ f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i),
        WoodinInverseStepRawComparison ξ j i p f.val) :
    ∀ i ∈ θ, IterationQuotientClosedBelow (forcingInverseCode θ (woodinIterationPrefix θ)) i θ
      ((woodinIterationCardinalPrefix θ) ‘ i) := by
  have hall := transfinite_induction
    (fun ξ : V ↦ ξ ⊆ θ → ∀ i ∈ ξ, IterationQuotientClosedBelow
      (forcingInverseCode ξ (woodinIterationPrefix ξ)) i ξ ((woodinIterationCardinalPrefix ξ) ‘ i))
    (by definability) ?_
  · exact hall (IsOrdinal.toOrdinal θ) (fun _ hx ↦ hx)
  intro ξ ih hξ i hi
  have hs' : ∀ k ∈ (ξ : V), IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)) := fun k hk ↦ hs k (hξ k hk)
  have hc' : ∀ k ∈ (ξ : V), HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)) := fun k hk ↦ hc k (hξ k hk)
  have h0' : (∅ : V) ∈ (ξ : V) :=
    empty_mem_of_ordinal_ne_empty (by rintro he; rw [he] at hi; exact not_mem_empty hi)
  refine woodinInverse_raw_quotient_closedBelow_decided hs' hc' h0' hi ?_ (hraw ξ hξ i hi)
  intro p hp f α hα hf j hj hij hlim hinac hprevn
  let := IsOrdinal.of_mem hj
  have hηval : (woodinIterationCardinalPrefix (ξ : V)) ‘ i =
      (kpair.π₂ (woodinIterationRec i)) ‘ i := woodinIterationCardinalPrefix_value_of_stages hs' hi
  have hηord : IsOrdinal ((kpair.π₂ (woodinIterationRec i)) ‘ i) :=
    hηval ▸ ((woodinIterationPrefix_of_stages hs').inaccessible i hi).1
  have hαord : IsOrdinal α := IsOrdinal.of_mem hα
  have hjθ : (j : V) ⊆ θ :=
    fun x hx ↦ hξ x (IsOrdinal.toIsTransitive.transitive _ hj x hx)
  exact woodinQuotientBoundAt_inverse_normalized_decided hs' hj hij hlim hinac
    (ih (IsOrdinal.toOrdinal j) hj hjθ) hα hp f hf (fun k hk ↦ (hprevn k hk).1)
    (hrawStep ξ hξ j hj i hij p f)

/-- The joint stage induction with the inverse-limit hypothesis discharged.

This is `woodinIteration_stages_of_inverse_closure` with its `hinverse` hypothesis replaced by
the two decided comparison premises. The proof is the same induction; at each stage the
per-stage families produced by the induction hypothesis feed
`woodinInverse_raw_closure_of_stages`. -/
theorem woodinIteration_stages_of_canonical_bound [Countable V] {δ : V}
    (hδ : IsWoodinSupercompact δ)
    (hraw : ∀ ξ : V, ξ ⊆ δ → ∀ i ∈ ξ, WoodinInverseRawComparison ξ i)
    (hrawStep : ∀ ξ : V, ξ ⊆ δ → ∀ j ∈ ξ, ∀ i ∈ j, ∀ p : V,
      ∀ f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i),
        WoodinInverseStepRawComparison ξ j i p f.val) :
    ∀ θ ∈ δ,
      IsWoodinIteration δ (succ θ) (kpair.π₁ (woodinIterationRec θ)) (kpair.π₂ (woodinIterationRec θ)) ∧
      HasWoodinQuotientClosure (succ θ) (kpair.π₁ (woodinIterationRec θ)) (kpair.π₂ (woodinIterationRec θ)) := by
  let := hδ.inaccessible.1
  have hall := transfinite_induction
    (fun ξ : V ↦ ξ ∈ δ →
      IsWoodinIteration δ (succ ξ) (kpair.π₁ (woodinIterationRec ξ)) (kpair.π₂ (woodinIterationRec ξ)) ∧
      HasWoodinQuotientClosure (succ ξ) (kpair.π₁ (woodinIterationRec ξ)) (kpair.π₂ (woodinIterationRec ξ)))
    (by definability) ?_
  · intro θ hθ
    let := IsOrdinal.of_mem hθ
    exact hall (IsOrdinal.toOrdinal θ) hθ
  intro θ ih hθ
  have hs : ∀ i ∈ (θ : V), IsWoodinIteration δ (succ i) (kpair.π₁ (woodinIterationRec i))
      (kpair.π₂ (woodinIterationRec i)) := by
    intro i hi
    let := IsOrdinal.of_mem hi
    exact (ih (IsOrdinal.toOrdinal i) hi (IsOrdinal.toIsTransitive.mem_trans hi hθ)).1
  have hc : ∀ i ∈ (θ : V), HasWoodinQuotientClosure (succ i) (kpair.π₁ (woodinIterationRec i))
      (kpair.π₂ (woodinIterationRec i)) := by
    intro i hi
    let := IsOrdinal.of_mem hi
    exact (ih (IsOrdinal.toOrdinal i) hi (IsOrdinal.toIsTransitive.mem_trans hi hθ)).2
  have hp := woodinIterationPrefix_of_stages hs
  have hpc := woodinIterationPrefix_quotient_closure hs hc
  have hθδ : (θ : V) ⊆ δ := IsOrdinal.toIsTransitive.transitive _ hθ
  have hi : (θ : V) ≠ ∅ → (∀ i ∈ (θ : V), succ i ∈ (θ : V)) →
      ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix (θ : V))) →
      ∀ i ∈ (θ : V), IterationQuotientClosedBelow
        (forcingInverseCode (θ : V) (woodinIterationPrefix (θ : V))) i (θ : V)
        ((woodinIterationCardinalPrefix (θ : V)) ‘ i) := by
    intro h0 _ _
    exact woodinInverse_raw_closure_of_stages hs hc (empty_mem_of_ordinal_ne_empty h0)
      (fun ξ hξ ↦ hraw ξ (fun x hx ↦ hθδ x (hξ x hx)))
      (fun ξ hξ ↦ hrawStep ξ (fun x hx ↦ hθδ x (hξ x hx)))
  rw [woodinIterationRec_rule]
  exact ⟨woodinStageRule_valid hδ hθ hp hpc hi, woodinStageRule_quotient_closure hδ hθ hp hpc hi⟩

/-- The exit datum for the Woodin iteration, conditional only on the two decided comparison
premises. -/
theorem woodinIterationExit_of_canonical_bound [Countable V] {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V)
    (hraw : ∀ ξ : V, ξ ⊆ δ → ∀ i ∈ ξ, WoodinInverseRawComparison ξ i)
    (hrawStep : ∀ ξ : V, ξ ⊆ δ → ∀ j ∈ ξ, ∀ i ∈ j, ∀ p : V,
      ∀ f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i),
        WoodinInverseStepRawComparison ξ j i p f.val) : WoodinIterationExit δ := by
  let := hδ.inaccessible.1
  have hs := woodinIteration_stages_of_canonical_bound hδ hraw hrawStep
  exact woodinIterationExit_of_stages hAC (fun θ hθ ↦ (hs θ hθ).1) (fun θ hθ ↦ (hs θ hθ).2)

end ZFVP
