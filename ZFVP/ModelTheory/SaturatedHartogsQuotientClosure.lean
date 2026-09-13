import ZFVP.ModelTheory.QuotientClosureComposition
import ZFVP.ModelTheory.SaturatedHartogsFormulas

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem saturatedHartogs_quotient_comp_closedAt_countable [Countable V]
    (A : ForcingContext V) {T U o τ E κ δ π : V}
    (hτ : IsForcingSplitProjection A.P A.R T U τ E)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o)
    (hδ : IsChoicelessInaccessible δ) (hT : T ∈ hierarchy δ) (hκδ : κ ∈ δ)
    (hκ : ∀ p ∈ T, p ∈ forcingFormula T U regularCardinalFormula (standardTuple ![hartogsNumberName T U (checkName o κ)]))
    (hπ : π ∈ A.P ^ twoStepConditions T U (saturatedHartogsPosetName T U o κ δ) ∅)
    (he : ∀ q ∈ twoStepConditions T U (saturatedHartogsPosetName T U o κ δ) ∅,
      τ ‘ ((twoStepProjection T U (saturatedHartogsPosetName T U o κ δ) ∅) ‘ q) = π ‘ q)
    {γ : A.Model} [IsOrdinal γ] (hγκ : γ ∈ A.check κ) (hDC : InternalDependentChoiceAt γ)
    (hbase : IsForcingClosedThrough (A.projectionQuotient T τ)
      (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) γ) :
    IsForcingClosedAt
      (A.projectionQuotient (twoStepConditions T U (saturatedHartogsPosetName T U o κ δ) ∅) π)
      (forcingSeparativeOrder
        (A.projectionQuotient (twoStepConditions T U (saturatedHartogsPosetName T U o κ δ) ∅) π)
        (A.projectionQuotientOrder
          (twoStepConditions T U (saturatedHartogsPosetName T U o κ δ) ∅)
          (twoStepOrder T U (saturatedHartogsPosetName T U o κ δ)
            (saturatedHartogsOrderName T U o κ δ) ∅) π)) γ := by
  have h := saturatedHartogsCollapse_iterand hU ho hδ hκ
  apply A.twoStep_collapse_quotient_comp_closedAt_countable hτ hU ho h hπ he γ hDC hbase
  intro H hH hA
  let C : ForcingContext V := ⟨T, U, o, H, hU, ho, hH⟩
  obtain ⟨p, hp⟩ := hH.1.2.1
  let ν : ForcingName T := ⟨checkName o κ, checkName_isName ho.1 _⟩
  have hv : C.ofName (C.hartogsName ν) = hartogsNumber (C.check κ) := C.hartogsName_value ν
  have hreg : IsRegularCardinal (hartogsNumber (C.check κ)) := by
    rw [← hv]
    exact
    (Defined.eval_iff _).mp ((C.formula_truth regularCardinalFormula
      ![C.hartogsName ν]).mpr ⟨p, hp, hκ p (hH.1.1 p hp)⟩)
  refine ⟨hartogsNumber (C.check κ), C.check δ, hreg, ?_,
    C.saturatedHartogsCollapseName_value hδ hT hκδ,
    C.saturatedHartogsCollapseOrderName_value hδ hT hκδ⟩
  have hκord : IsOrdinal κ := by
    let := hδ.1
    exact IsOrdinal.of_mem hκδ
  let := hκord
  have hm : A.projectionInclusion C hτ hA γ ∈ C.check κ := by
    rw [← A.projectionInclusion_check C hτ hA κ]
    exact (A.projectionInclusion C hτ hA).mem_iff γ (A.check κ) |>.mpr hγκ
  let := IsOrdinal.of_mem hm
  exact ordinal_cardLE_iff_mem_hartogsNumber.mp
    (cardLE_of_subset (IsOrdinal.toIsTransitive.transitive _ hm))


theorem saturatedHartogs_quotient_comp_closedBelow_countable [Countable V]
    (A : ForcingContext V) {T U o τ E κ δ π : V}
    (hτ : IsForcingSplitProjection A.P A.R T U τ E)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o)
    (hδ : IsChoicelessInaccessible δ) (hT : T ∈ hierarchy δ) (hκδ : κ ∈ δ)
    (hκ : ∀ p ∈ T, p ∈ forcingFormula T U regularCardinalFormula (standardTuple ![hartogsNumberName T U (checkName o κ)]))
    (hπ : π ∈ A.P ^ twoStepConditions T U (saturatedHartogsPosetName T U o κ δ) ∅)
    (he : ∀ q ∈ twoStepConditions T U (saturatedHartogsPosetName T U o κ δ) ∅,
      τ ‘ ((twoStepProjection T U (saturatedHartogsPosetName T U o κ δ) ∅) ‘ q) = π ‘ q)
    {η : A.Model} [IsOrdinal η] (hηκ : η ⊆ A.check κ)
    (hDC : ∀ γ ∈ η, InternalDependentChoiceAt γ)
    (hbase : IsForcingClosedBelow (A.projectionQuotient T τ)
      (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) η) :
    IsForcingClosedBelow
      (A.projectionQuotient (twoStepConditions T U (saturatedHartogsPosetName T U o κ δ) ∅) π)
      (forcingSeparativeOrder
        (A.projectionQuotient (twoStepConditions T U (saturatedHartogsPosetName T U o κ δ) ∅) π)
        (A.projectionQuotientOrder
          (twoStepConditions T U (saturatedHartogsPosetName T U o κ δ) ∅)
          (twoStepOrder T U (saturatedHartogsPosetName T U o κ δ)
            (saturatedHartogsOrderName T U o κ δ) ∅) π)) η := by
  intro γ hγ
  let := IsOrdinal.of_mem hγ
  apply A.saturatedHartogs_quotient_comp_closedAt_countable hτ hU ho hδ hT hκδ hκ hπ he
    (hηκ γ hγ) (hDC γ hγ)
  intro α hα hαγ
  let := hα
  exact hbase α (ordinal_mem_of_subset_mem hαγ hγ)

end ForcingContext
end ZFVP
