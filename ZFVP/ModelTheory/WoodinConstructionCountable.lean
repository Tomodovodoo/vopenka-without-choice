import ZFVP.ModelTheory.WoodinRawInverseClosure
import ZFVP.ModelTheory.WoodinStageInduction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinRawInverse_code_quotient_closedBelow [Countable V] {δ θ i : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hc : ∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hi : i ∈ θ) :
    IterationQuotientClosedBelow (forcingInverseCode θ (woodinIterationPrefix θ)) i θ
      ((woodinIterationCardinalPrefix θ) ‘ i) := by
  simpa only [IterationQuotientClosedBelow, forcingInverseCode, forcingThreadCode, forcingIterationCodeNext,
    forcingCodeP_code, forcingCodeR_code, forcingCodet_code, forcingCodeπ_code,
    forcingFamilyNext_old hi, forcingFamilyNext_new, forcingMatrixNext_column hi,
    forcingLimitProjectionColumn_value hi, forcingInverseCodePoset, forcingInverseCodeOrder]
    using woodinRawInverse_quotient_closedBelow hs hc hi

theorem woodinIteration_stages_countable [Countable V] {δ : V} (hδ : IsWoodinSupercompact δ) :
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
  have hi := fun (_ : (θ : V) ≠ ∅) (_ : ∀ i ∈ (θ : V), succ i ∈ (θ : V))
    (_ : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix (θ : V))))
    (i : V) (hi : i ∈ (θ : V)) ↦ woodinRawInverse_code_quotient_closedBelow hs hc hi
  rw [woodinIterationRec_rule]
  exact ⟨woodinStageRule_valid hδ hθ hp hpc hi, woodinStageRule_quotient_closure hδ hθ hp hpc hi⟩

theorem woodinIterationExit_countable [Countable V] {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) : WoodinIterationExit δ := by
  let := hδ.inaccessible.1
  have hs := woodinIteration_stages_countable hδ
  exact woodinIterationExit_of_stages hAC (fun θ hθ ↦ (hs θ hθ).1) (fun θ hθ ↦ (hs θ hθ).2)

theorem woodinIterationConstruction_countable [Countable V] : WoodinIterationConstruction (V := V) :=
  fun _ hδ hAC ↦ woodinIterationExit_countable hδ hAC

end ZFVP