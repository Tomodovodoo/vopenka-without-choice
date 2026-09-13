import ZFVP.ModelTheory.QuotientClosureComposition
import ZFVP.ModelTheory.SaturatedWoodinSuccessor

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem saturatedWoodin_quotient_closedAt (A : ForcingContext V) {κ δ : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hκδ : κ ⊆ δ)
    (hκ : ∀ p ∈ A.P, p ∈ forcingFormula A.P A.R regularCardinalFormula
      (standardTuple ![checkName A.one κ]))
    {α : A.Model} (hα : α ∈ A.check κ) (hDC : InternalDependentChoiceAt α) :
    IsForcingClosedAt
      (A.projectionQuotient (twoStepConditions A.P A.R (saturatedWoodinPrefixPosetName A.P A.R A.one κ δ) ∅)
        (twoStepProjection A.P A.R (saturatedWoodinPrefixPosetName A.P A.R A.one κ δ) ∅))
      (forcingSeparativeOrder
        (A.projectionQuotient (twoStepConditions A.P A.R (saturatedWoodinPrefixPosetName A.P A.R A.one κ δ) ∅)
          (twoStepProjection A.P A.R (saturatedWoodinPrefixPosetName A.P A.R A.one κ δ) ∅))
        (A.projectionQuotientOrder
          (twoStepConditions A.P A.R (saturatedWoodinPrefixPosetName A.P A.R A.one κ δ) ∅)
          (twoStepOrder A.P A.R (saturatedWoodinPrefixPosetName A.P A.R A.one κ δ)
            (saturatedWoodinPrefixOrderName A.P A.R A.one κ δ) ∅)
          (twoStepProjection A.P A.R (saturatedWoodinPrefixPosetName A.P A.R A.one κ δ) ∅))) α := by
  have h := saturatedWoodinPrefix_iterand A.order A.top hδ hP hκδ hκ
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  have hreg : IsRegularCardinal (A.check κ) :=
    (Defined.eval_iff _).mp ((A.formula_truth regularCardinalFormula
      ![⟨checkName A.one κ, checkName_isName A.top.1 κ⟩]).mpr
        ⟨p, hp, hκ p (A.generic.1.1 p hp)⟩)
  exact A.twoStep_collapse_quotient_closedAt h (A.saturatedWoodinPosetName_value hδ hP hκδ)
    (A.saturatedWoodinOrderName_value hδ hP hκδ) hreg hα hDC

theorem saturatedWoodin_quotient_comp_closedAt_countable [Countable V]
    (A : ForcingContext V) {T U o τ E κ δ π : V}
    (hτ : IsForcingSplitProjection A.P A.R T U τ E)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o)
    (hδ : IsChoicelessInaccessible δ) (hT : T ∈ hierarchy δ) (hκδ : κ ⊆ δ)
    (hκ : ∀ p ∈ T, p ∈ forcingFormula T U regularCardinalFormula (standardTuple ![checkName o κ]))
    (hπ : π ∈ A.P ^ twoStepConditions T U (saturatedWoodinPrefixPosetName T U o κ δ) ∅)
    (he : ∀ q ∈ twoStepConditions T U (saturatedWoodinPrefixPosetName T U o κ δ) ∅,
      τ ‘ ((twoStepProjection T U (saturatedWoodinPrefixPosetName T U o κ δ) ∅) ‘ q) = π ‘ q)
    {γ : A.Model} [IsOrdinal γ] (hγκ : γ ∈ A.check κ) (hDC : InternalDependentChoiceAt γ)
    (hbase : IsForcingClosedThrough (A.projectionQuotient T τ)
      (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) γ) :
    IsForcingClosedAt
      (A.projectionQuotient (twoStepConditions T U (saturatedWoodinPrefixPosetName T U o κ δ) ∅) π)
      (forcingSeparativeOrder
        (A.projectionQuotient (twoStepConditions T U (saturatedWoodinPrefixPosetName T U o κ δ) ∅) π)
        (A.projectionQuotientOrder
          (twoStepConditions T U (saturatedWoodinPrefixPosetName T U o κ δ) ∅)
          (twoStepOrder T U (saturatedWoodinPrefixPosetName T U o κ δ)
            (saturatedWoodinPrefixOrderName T U o κ δ) ∅) π)) γ := by
  have h := saturatedWoodinPrefix_iterand hU ho hδ hT hκδ hκ
  apply A.twoStep_collapse_quotient_comp_closedAt_countable hτ hU ho h hπ he γ hDC hbase
  intro H hH hA
  let C : ForcingContext V := ⟨T, U, o, H, hU, ho, hH⟩
  obtain ⟨p, hp⟩ := hH.1.2.1
  have hreg : IsRegularCardinal (C.check κ) :=
    (Defined.eval_iff _).mp ((C.formula_truth regularCardinalFormula
      ![⟨checkName o κ, checkName_isName ho.1 κ⟩]).mpr ⟨p, hp, hκ p (hH.1.1 p hp)⟩)
  refine ⟨C.check κ, C.check δ, hreg, ?_, C.saturatedWoodinPosetName_value hδ hT hκδ,
    C.saturatedWoodinOrderName_value hδ hT hκδ⟩
  rw [← A.projectionInclusion_check C hτ hA κ]
  exact (A.projectionInclusion C hτ hA).mem_iff γ (A.check κ) |>.mpr hγκ

theorem saturatedWoodin_quotient_comp_closedBelow_countable [Countable V]
    (A : ForcingContext V) {T U o τ E κ δ π : V}
    (hτ : IsForcingSplitProjection A.P A.R T U τ E)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o)
    (hδ : IsChoicelessInaccessible δ) (hT : T ∈ hierarchy δ) (hκδ : κ ⊆ δ)
    (hκ : ∀ p ∈ T, p ∈ forcingFormula T U regularCardinalFormula (standardTuple ![checkName o κ]))
    (hπ : π ∈ A.P ^ twoStepConditions T U (saturatedWoodinPrefixPosetName T U o κ δ) ∅)
    (he : ∀ q ∈ twoStepConditions T U (saturatedWoodinPrefixPosetName T U o κ δ) ∅,
      τ ‘ ((twoStepProjection T U (saturatedWoodinPrefixPosetName T U o κ δ) ∅) ‘ q) = π ‘ q)
    {η : A.Model} [IsOrdinal η] (hηκ : η ⊆ A.check κ)
    (hDC : ∀ γ ∈ η, InternalDependentChoiceAt γ)
    (hbase : IsForcingClosedBelow (A.projectionQuotient T τ)
      (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) η) :
    IsForcingClosedBelow
      (A.projectionQuotient (twoStepConditions T U (saturatedWoodinPrefixPosetName T U o κ δ) ∅) π)
      (forcingSeparativeOrder
        (A.projectionQuotient (twoStepConditions T U (saturatedWoodinPrefixPosetName T U o κ δ) ∅) π)
        (A.projectionQuotientOrder
          (twoStepConditions T U (saturatedWoodinPrefixPosetName T U o κ δ) ∅)
          (twoStepOrder T U (saturatedWoodinPrefixPosetName T U o κ δ)
            (saturatedWoodinPrefixOrderName T U o κ δ) ∅) π)) η := by
  intro γ hγ
  let := IsOrdinal.of_mem hγ
  apply A.saturatedWoodin_quotient_comp_closedAt_countable hτ hU ho hδ hT hκδ hκ hπ he
    (hηκ γ hγ) (hDC γ hγ)
  intro α hα hαγ
  let := hα
  exact hbase α (ordinal_mem_of_subset_mem hαγ hγ)

end ForcingContext
end ZFVP
