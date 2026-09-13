import ZFVP.ModelTheory.RankCollapseCombinedContext
import ZFVP.ModelTheory.TwoStepInclusion
import ZFVP.SetTheory.WoodinCollapseRetraction
import ZFVP.ModelTheory.WoodinCollapsePreservation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]

namespace ForcingContext
variable (A : ForcingContext V) {κ c δ : V}
  (hc : IsChoicelessInaccessible c) (hδ : IsChoicelessInaccessible δ)
  (hP : A.P ∈ hierarchy c) (hPδ : A.P ∈ hierarchy δ)
  (hκc : κ ⊆ c) (hκδ : κ ⊆ δ) (hcδ : c ⊆ δ) (hz : (∅ : V) ∈ κ)
  {Hc Hδ : Set A.Model}
  (hHc : IsExternalForcingGeneric (woodinCollapse (A.check κ) (A.check c))
    (woodinCollapseOrder (A.check κ) (A.check c)) Hc)
  (hHδ : IsExternalForcingGeneric (woodinCollapse (A.check κ) (A.check δ))
    (woodinCollapseOrder (A.check κ) (A.check δ)) Hδ)
  (hH : ∀ p, p ∈ Hc ↔ p ∈ Hδ ∧ p ∈ woodinCollapse (A.check κ) (A.check c))

include hcδ hH

theorem rankCollapse_combined_restrict_of_filter (z : V) :
    z ∈ (A.rankCollapseCombinedContext hc hP hκc hz hHc).G ↔
      z ∈ (A.rankCollapseCombinedContext hδ hPδ hκδ hz hHδ).G ∧
        z ∈ (A.rankCollapseCombinedContext hc hP hκc hz hHc).P := by
  apply twoStepCombinedFilter_restrict A (rankCollapseName_isName _ _ _ _ _)
    (rankCollapseName_mono_countable A.order A.top hc hδ hP hκc hcδ)
  intro x
  change (x ∈ Hc ↔ x ∈ Hδ ∧ x ∈ A.ofName (A.rankCollapse κ c))
  rw [A.rankCollapse_value hc hP hκc]
  exact hH x

theorem rankCollapse_combined_function_of_closed
    (hκ : IsRegularCardinal (A.check κ))
    (hDC : ∀ α ∈ A.check κ, InternalDependentChoiceAt α)
    {γ : V} (hγ : γ ∈ κ)
    {X : (A.rankCollapseCombinedContext hc hP hκc hz hHc).Model}
    {f : (A.rankCollapseCombinedContext hδ hPδ hκδ hz hHδ).Model}
    (hf : f ∈ (A.rankCollapseCombinedContext hc hP hκc hz hHc).genericInclusion
      (A.rankCollapseCombinedContext hδ hPδ hκδ hz hHδ)
      (A.rankCollapse_combined_restrict_of_filter hc hδ hP hPδ hκc hκδ hcδ hz hHc hHδ hH) X ^
        (A.rankCollapseCombinedContext hδ hPδ hκδ hz hHδ).check γ) :
    ∃ g ∈ X ^ (A.rankCollapseCombinedContext hc hP hκc hz hHc).check γ,
      (A.rankCollapseCombinedContext hc hP hκc hz hHc).genericInclusion
        (A.rankCollapseCombinedContext hδ hPδ hκδ hz hHδ)
        (A.rankCollapse_combined_restrict_of_filter hc hδ hP hPδ hκc hκδ hcδ hz hHc hHδ hH) g = f := by
  let := hδ.1
  let := hc.1
  let ihc := rankCollapse_iterand_countable A.order A.top hc hP hκc hz
  let ihδ := rankCollapse_iterand_countable A.order A.top hδ hPδ hκδ hz
  let gc := A.rankCollapse_generic hc hP hκc hHc
  let gδ := A.rankCollapse_generic hδ hPδ hκδ hHδ
  let T := TwoStepModel.iterandContext A ihc gc
  let U := TwoStepModel.iterandContext A ihδ gδ
  have hTP : T.P = woodinCollapse (A.check κ) (A.check c) := A.rankCollapse_value hc hP hκc
  have hUP : U.P = woodinCollapse (A.check κ) (A.check δ) := A.rankCollapse_value hδ hPδ hκδ
  have hTR : T.R = woodinCollapseOrder (A.check κ) (A.check c) := A.rankCollapseOrder_value hc hP hκc
  have hUR : U.R = woodinCollapseOrder (A.check κ) (A.check δ) := A.rankCollapseOrder_value hδ hPδ hκδ
  have hs : A.check c ⊆ A.check δ := (A.checkEmbedding.subset_iff _ _).mpr hcδ
  have hπ : IsForcingRetraction T.P T.R U.P U.R
      (woodinCollapseProjection (A.check κ) (A.check c) (A.check δ)) := by
    rw [hTP, hTR, hUP, hUR]
    exact woodinCollapse_retraction hκ (A.check_inaccessible_of_small hc hP).regular hs
  have ht : ∀ p, p ∈ T.G ↔ p ∈ U.G ∧ p ∈ T.P := by
    intro p
    change p ∈ Hc ↔ p ∈ Hδ ∧ p ∈ T.P
    rw [hTP]
    exact hH p
  have hγ' : A.check γ ∈ A.check κ := (A.check_mem_iff _ _).mpr hγ
  let := hκ.1.1
  let := IsOrdinal.of_mem hγ'
  apply TwoStepModel.inclusion_function_of_tail_closed A ihc ihδ gc gδ _ hπ ht rfl
    (IsOrdinal.of_mem hγ') (hDC _ hγ') ?_ hf
  intro α hα hαγ
  change IsForcingClosedAt U.P U.R α
  rw [hUP, hUR]
  let := hα
  exact woodinCollapse_closedBelow hκ hDC (A.check δ) α (ordinal_mem_of_subset_mem hαγ hγ')

end ForcingContext
end ZFVP
