import ZFVP.ModelTheory.WoodinStageRuleClosure
import ZFVP.ModelTheory.WoodinHistoryQuotientClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance iterationQuotientClosedBelow_definable : ℒₛₑₜ-relation₄[V] IterationQuotientClosedBelow := by
  exact Language.Definable.substitution
    (f := ![(fun v : Fin 4 → V ↦ (forcingCodeP (v 0)) ‘ (v 1)),
      (fun v ↦ (forcingCodeR (v 0)) ‘ (v 1)),
      (fun v ↦ (forcingCodet (v 0)) ‘ (v 1)),
      (fun v ↦ (forcingCodeP (v 0)) ‘ (v 2)),
      (fun v ↦ (forcingCodeR (v 0)) ‘ (v 2)),
      (fun v ↦ (forcingCodeπ (v 0)) ‘ ⟨v 1, v 2⟩ₖ),
      (fun v ↦ v 3)])
    allProjectionQuotientClosedBelowFormula_defined.to_definable
    (by simp only [Fin.forall_fin_succ]; repeat' constructor <;> definability)

instance hasWoodinQuotientClosure_definable : ℒₛₑₜ-relation₃[V] HasWoodinQuotientClosure := by
  unfold HasWoodinQuotientClosure
  definability

/-- The joint induction is conditional only on closure of raw inverse quotients
at the actual recursive prefixes. WoodinConstructionCountable supplies the raw
closure step during the induction; WoodinConstruction transfers its endpoint. -/
theorem woodinIteration_stages_of_inverse_closure {δ : V}
    (hδ : IsWoodinSupercompact δ)
    (hinverse : ∀ θ ∈ δ, θ ≠ ∅ → (∀ i ∈ θ, succ i ∈ θ) →
      IsWoodinIteration δ θ (woodinIterationPrefix θ) (woodinIterationCardinalPrefix θ) →
      HasWoodinQuotientClosure θ (woodinIterationPrefix θ) (woodinIterationCardinalPrefix θ) →
      ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)) →
      ∀ i ∈ θ, IterationQuotientClosedBelow (forcingInverseCode θ (woodinIterationPrefix θ))
        i θ ((woodinIterationCardinalPrefix θ) ‘ i)) :
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
  have hi := fun h0 hl hn ↦ hinverse θ hθ h0 hl hp hpc hn
  rw [woodinIterationRec_rule]
  exact ⟨woodinStageRule_valid hδ hθ hp hpc hi, woodinStageRule_quotient_closure hδ hθ hp hpc hi⟩

theorem woodinIterationExit_of_inverse_closure {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V)
    (hinverse : ∀ θ ∈ δ, θ ≠ ∅ → (∀ i ∈ θ, succ i ∈ θ) →
      IsWoodinIteration δ θ (woodinIterationPrefix θ) (woodinIterationCardinalPrefix θ) →
      HasWoodinQuotientClosure θ (woodinIterationPrefix θ) (woodinIterationCardinalPrefix θ) →
      ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)) →
      ∀ i ∈ θ, IterationQuotientClosedBelow (forcingInverseCode θ (woodinIterationPrefix θ))
        i θ ((woodinIterationCardinalPrefix θ) ‘ i)) : WoodinIterationExit δ := by
  let := hδ.inaccessible.1
  have hs := woodinIteration_stages_of_inverse_closure hδ hinverse
  exact woodinIterationExit_of_stages hAC (fun θ hθ ↦ (hs θ hθ).1) (fun θ hθ ↦ (hs θ hθ).2)

end ZFVP
