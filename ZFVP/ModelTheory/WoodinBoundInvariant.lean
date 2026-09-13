import ZFVP.ModelTheory.ProjectionQuotientSequenceForcing
import ZFVP.ModelTheory.WoodinQuotientBoundRecursion
import ZFVP.ModelTheory.WoodinQuotientBoundEquations

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def ForcesWoodinQuotientSequence (θ i p f α : V) : Prop :=
  let s := kpair.π₁ (woodinIterationRec i)
  let B := (forcingCodeP s) ‘ i
  let R := (forcingCodeR s) ‘ i
  let b := (forcingCodet s) ‘ i
  let D := forcingInverseCodePoset θ (woodinIterationPrefix θ)
  let U := forcingInverseCodeOrder θ (woodinIterationPrefix θ)
  let π := forcingThreadCoordinate D i
  p ∈ forcingFormula B R forcingSeparativeDescendingFormula
    (standardTuple ![projectionQuotientName D π b, projectionQuotientOrderName U π b, checkName b α, f])

/-- The induction property is a formula in the ground model. In particular,
its bound clause does not quantify over external generics. -/
def IsWoodinQuotientBoundAt (θ i p f α j : V) : Prop :=
  let s := woodinIterationPrefix θ
  let B := (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i
  let R := (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i
  let b := (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i
  let P := (forcingCodeP s) ‘ j
  let S := (forcingCodeR s) ‘ j
  let π := (forcingCodeπ s) ‘ ⟨i, j⟩ₖ
  let q := woodinQuotientBoundRec θ i p f j
  q ∈ P ∧ (i ⊆ j → p ∈ forcingFormula B R forcingSeparativeBoundFormula
    (standardTuple ![projectionQuotientName P π b, projectionQuotientOrderName S π b,
      checkName b α, woodinBoundCoordinateName θ i f j, checkName b q]))

instance isWoodinQuotientBoundAt_definable (θ i p f α : V) :
    ℒₛₑₜ-predicate[V] (IsWoodinQuotientBoundAt θ i p f α) := by
  unfold IsWoodinQuotientBoundAt
  dsimp only
  apply Language.Definable.and
  · definability
  · apply Language.Definable.imp
    · definability
    · apply Language.DefinableRel₄.comp
        (P := fun p B R v ↦ p ∈ forcingFormula B R forcingSeparativeBoundFormula v)
      · definability
      · definability
      · definability
      · simp only [standardTuple]
        definability

end ZFVP
