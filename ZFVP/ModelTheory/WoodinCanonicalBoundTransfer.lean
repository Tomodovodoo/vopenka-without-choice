import ZFVP.ModelTheory.WoodinInvariantUniform
import ZFVP.ModelTheory.WoodinCanonicalBoundClosed
import ZFVP.ModelTheory.WoodinIterationContract

/-! Reducing the Woodin iteration contract to one countability-free statement.

This file retains Fable's earlier conditional transfer route. The integrated
`WoodinConstruction` and `WoodinInvariantUniform` modules already provide the
later construction and uniform formulas. The missing-step descriptions below
refer to the earlier route, not to the status of the combined development.
Part B reuses the shared canonical formulas through compatibility instances.

`woodinInverse_raw_closure_of_stages_closed` and `woodinIterationExit_of_stages_closed` in
`ZFVP/ModelTheory/WoodinCanonicalBoundClosed.lean` carry `[Countable V]`, inherited from the
generic-filter steps of the bound induction. The contract target `WoodinIterationConstruction` in
`ZFVP/ModelTheory/WoodinIterationContract.lean` has no such hypothesis.

Part A confines the countability to a single statement. `WoodinInverseRawClosure` is the
inverse-limit closure exactly as `woodinInverse_raw_closure_of_stages_closed` states it, with
`[Countable V]` dropped. The joint stage induction and the exit derivation need no countability of
their own, so `woodinIterationConstruction_of_rawClosure` reaches the contract target from
`WoodinInverseRawClosure` alone.

Part B supplies parameter-free defining semisentences for the operators of that statement's
conclusion: `forcingCodeP`, `forcingCodeR`, `forcingCodeπ`, `forcingCodet`,
`IterationQuotientClosedBelow` and `HasWoodinQuotientClosure`. A Löwenheim-Skolem transfer of the
shape used in `ZFVP/ModelTheory/SaturatedQuotientClosureTransfer.lean` needs these, and the
development so far has for them only `Language.Definable` instances, which are existential in a
formula with parameters and so say nothing across two models.

The transfer itself is not completed. The note before `WoodinInverseRawClosure` lists the
operators whose defining formulas are still missing and where they would go. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Part A: the countability confined to one statement -/

/-- The inverse-limit closure of the Woodin iteration at every ambient index, with no countability
hypothesis. This is the statement of `woodinInverse_raw_closure_of_stages_closed` with
`[Countable V]` dropped and `[IsOrdinal θ]` turned into an argument, so that the whole thing is a
`Prop` about `V`.

Transferring this by the route of `SaturatedQuotientClosureTransfer.lean` needs it written as one
`SetTheorySemisentence`. Part B below gives the formulas for the conclusion. Still missing, and
needed before the sentence can be written, are defining semisentences for

* `woodinIterationRec`, `woodinIterationPrefix` and `woodinIterationCardinalPrefix`
  (`ZFVP/ModelTheory/WoodinIterationRecursion.lean`). The recursion is not the obstacle:
  `transfiniteRecFormula` in `ZFVP/SetTheory/UniformRecursion.lean` turns a formula for the step
  into one for the recursion, as it does for `hierarchy`. What is missing is a formula for
  `woodinIterationRecursionStep`, hence for `woodinStageRule`
  (`ZFVP/ModelTheory/WoodinStageRule.lean`) and for each of its four branches
  `woodinInitialCode`, `woodinIterationSuccessor`, `forcingDirectCode` and
  `woodinInverseSourceCode`, together with the code and name constructors under them;
* `forcingInverseCode` (`ZFVP/ModelTheory/ForcingLimitCode.lean`), and under it
  `forcingThreadCode`, `forcingIterationCodeNext` and the three limit columns;
* `IsWoodinIteration` (`ZFVP/ModelTheory/WoodinIterationInvariant.lean`), and under it
  `IsForcingIterationCode`, `IsIterationTable`, `IsWoodinStage` and `IsWoodinStageSmall`. -/
def WoodinInverseRawClosure (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  ∀ δ θ : V, IsOrdinal θ →
    (∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) →
    (∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) →
    ∀ i ∈ θ, IterationQuotientClosedBelow (forcingInverseCode θ (woodinIterationPrefix θ)) i θ
      ((woodinIterationCardinalPrefix θ) ‘ i)

/-- In a countable model the closure statement holds. This is
`woodinInverse_raw_closure_of_stages_closed` packaged as `WoodinInverseRawClosure`. -/
theorem woodinInverseRawClosure_of_countable [Countable V] : WoodinInverseRawClosure V := by
  intro δ θ hθ hs hc
  let := hθ
  exact woodinInverse_raw_closure_of_stages_closed hs hc

/-- The joint stage induction from the closure statement alone, with no countability. This is
`woodinIteration_stages_of_stages_closed` with its call to
`woodinInverse_raw_closure_of_stages_closed` replaced by the hypothesis `hclosure`. -/
theorem woodinIteration_stages_of_rawClosure (hclosure : WoodinInverseRawClosure V) {δ : V}
    (hδ : IsWoodinSupercompact δ) :
    ∀ θ ∈ δ,
      IsWoodinIteration δ (succ θ) (kpair.π₁ (woodinIterationRec θ))
        (kpair.π₂ (woodinIterationRec θ)) ∧
      HasWoodinQuotientClosure (succ θ) (kpair.π₁ (woodinIterationRec θ))
        (kpair.π₂ (woodinIterationRec θ)) := by
  let := hδ.inaccessible.1
  have hall := transfinite_induction
    (fun ξ : V ↦ ξ ∈ δ →
      IsWoodinIteration δ (succ ξ) (kpair.π₁ (woodinIterationRec ξ))
        (kpair.π₂ (woodinIterationRec ξ)) ∧
      HasWoodinQuotientClosure (succ ξ) (kpair.π₁ (woodinIterationRec ξ))
        (kpair.π₂ (woodinIterationRec ξ)))
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
  have hi : (θ : V) ≠ ∅ → (∀ i ∈ (θ : V), succ i ∈ (θ : V)) →
      ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix (θ : V))) →
      ∀ i ∈ (θ : V), IterationQuotientClosedBelow
        (forcingInverseCode (θ : V) (woodinIterationPrefix (θ : V))) i (θ : V)
        ((woodinIterationCardinalPrefix (θ : V)) ‘ i) :=
    fun _ _ _ ↦ hclosure δ (θ : V) inferInstance hs hc
  rw [woodinIterationRec_rule]
  exact ⟨woodinStageRule_valid hδ hθ hp hpc hi, woodinStageRule_quotient_closure hδ hθ hp hpc hi⟩

/-- The exit datum from the closure statement alone, with no countability. -/
theorem woodinIterationExit_of_rawClosure (hclosure : WoodinInverseRawClosure V) {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) : WoodinIterationExit δ := by
  let := hδ.inaccessible.1
  have hs := woodinIteration_stages_of_rawClosure hclosure hδ
  exact woodinIterationExit_of_stages hAC (fun θ hθ ↦ (hs θ hθ).1) (fun θ hθ ↦ (hs θ hθ).2)

/-- The contract target of `ZFVP/ModelTheory/WoodinIterationContract.lean` from the closure
statement alone, with no countability. -/
theorem woodinIterationConstruction_of_rawClosure (hclosure : WoodinInverseRawClosure V) :
    WoodinIterationConstruction (V := V) :=
  fun _ hδ hAC ↦ woodinIterationExit_of_rawClosure hclosure hδ hAC

/-- The contract target in a countable model. -/
theorem woodinIterationConstruction_of_countable [Countable V] :
    WoodinIterationConstruction (V := V) :=
  woodinIterationConstruction_of_rawClosure woodinInverseRawClosure_of_countable

/-! The uniform formulas and their interpretation theorems are imported from
`WoodinInvariantUniform`. These names retain the earlier accessor interfaces. -/

instance forcingCodeP_defined : ℒₛₑₜ-function₁[V] forcingCodeP via forcingCodePFormula := inferInstance
instance forcingCodeR_defined : ℒₛₑₜ-function₁[V] forcingCodeR via forcingCodeRFormula := inferInstance
instance forcingCodeπ_defined : ℒₛₑₜ-function₁[V] forcingCodeπ via forcingCodeπFormula := inferInstance
instance forcingCodet_defined : ℒₛₑₜ-function₁[V] forcingCodet via forcingCodetFormula := inferInstance

end ZFVP
