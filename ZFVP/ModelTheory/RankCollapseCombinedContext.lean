import ZFVP.ModelTheory.ForcingRankCollapseOrder
import ZFVP.ModelTheory.TwoStepCombinedGeneric
import ZFVP.ModelTheory.WoodinCollapseInitialGeneric

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext
variable (A : ForcingContext V)

theorem rankCollapse_generic {κ δ : V} (hδ : IsChoicelessInaccessible δ)
    (hP : A.P ∈ hierarchy δ) (hκ : κ ⊆ δ) {H : Set A.Model}
    (hH : IsExternalForcingGeneric (woodinCollapse (A.check κ) (A.check δ))
      (woodinCollapseOrder (A.check κ) (A.check δ)) H) :
    IsExternalForcingGeneric (A.ofName (A.rankCollapse κ δ))
      (A.ofName (A.rankOrder δ (A.rankCollapse κ δ))) H := by
  rw [A.rankCollapse_value hδ hP hκ, A.rankCollapseOrder_value hδ hP hκ]
  exact hH

noncomputable def rankCollapseCombinedContext [Countable V] {κ δ : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hκ : κ ⊆ δ)
    (hz : (∅ : V) ∈ κ) {H : Set A.Model}
    (hH : IsExternalForcingGeneric (woodinCollapse (A.check κ) (A.check δ))
      (woodinCollapseOrder (A.check κ) (A.check δ)) H) : ForcingContext V :=
  TwoStepModel.combinedContext A (rankCollapse_iterand_countable A.order A.top hδ hP hκ hz)
    (A.rankCollapse_generic hδ hP hκ hH)

theorem rankCollapse_initial_generic {κ c δ : V}
    (hc : IsChoicelessInaccessible c) (hP : A.P ∈ hierarchy c)
    (hκ : IsRegularCardinal (A.check κ)) [IsOrdinal δ] (hcδ : c ⊆ δ)
    {H : Set A.Model}
    (hH : IsExternalForcingGeneric (woodinCollapse (A.check κ) (A.check δ))
      (woodinCollapseOrder (A.check κ) (A.check δ)) H) :
    IsExternalForcingGeneric (woodinCollapse (A.check κ) (A.check c))
      (woodinCollapseOrder (A.check κ) (A.check c))
      (woodinCollapseInitialGeneric (A.check κ) (A.check c) H) := by
  have hs : A.check c ⊆ A.check δ := (A.checkEmbedding.subset_iff _ _).mpr hcδ
  exact woodinCollapse_initial_generic hκ (A.check_inaccessible_of_small hc hP).regular hs hH

theorem rankCollapse_combined_restrict [Countable V] {κ c δ : V}
    (hc : IsChoicelessInaccessible c) (hδ : IsChoicelessInaccessible δ)
    (hP : A.P ∈ hierarchy c) (hκ : κ ⊆ c) (hcδ : c ⊆ δ) (H : Set A.Model) (z : V) :
    z ∈ twoStepCombinedFilter A (rankCollapseName A.P A.R A.one κ c) ∅
        (woodinCollapseInitialGeneric (A.check κ) (A.check c) H) ↔
      z ∈ twoStepCombinedFilter A (rankCollapseName A.P A.R A.one κ δ) ∅ H ∧
        z ∈ twoStepConditions A.P A.R (rankCollapseName A.P A.R A.one κ c) ∅ := by
  apply twoStepCombinedFilter_restrict A (rankCollapseName_isName _ _ _ _ _)
    (rankCollapseName_mono_countable A.order A.top hc hδ hP hκ hcδ)
  intro x
  change (x ∈ H ∧ x ∈ woodinCollapse (A.check κ) (A.check c)) ↔
    x ∈ H ∧ x ∈ A.ofName (A.rankCollapse κ c)
  rw [A.rankCollapse_value hc hP hκ]

end ForcingContext
end ZFVP
