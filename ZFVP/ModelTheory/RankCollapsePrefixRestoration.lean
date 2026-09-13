import ZFVP.ModelTheory.RankCollapseCombinedRestoration
import ZFVP.ModelTheory.WoodinCollapseRestorationBelow
import ZFVP.ModelTheory.WoodinCollapseForcesRestoration

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]

namespace ForcingContext
variable (A : ForcingContext V) {κ δ : V}
  (hδ : IsWoodinSupercompact δ) (hP : A.P ∈ hierarchy δ) (hR : A.R ∈ hierarchy δ)
  (hκδ : κ ∈ δ) (hκ : IsRegularCardinal (A.check κ))
  (hDC : ∀ α ∈ A.check κ, InternalDependentChoiceAt α) {H : Set A.Model}
  (hH : IsExternalForcingGeneric (woodinCollapse (A.check κ) (A.check δ))
    (woodinCollapseOrder (A.check κ) (A.check δ)) H)

include hδ hP hR hκδ hκ hDC

theorem rankCollapse_tail_dependentChoiceAt :
    InternalDependentChoiceAt ((woodinCollapseContext hκ (A.check δ) H hH).check (A.check κ)) := by
  let := hδ.1.1
  have hs : κ ⊆ δ := IsOrdinal.toIsTransitive.transitive _ hκδ
  have hz : (∅ : V) ∈ κ := (A.check_mem_iff _ _).mp (by
    rw [A.check_empty]
    exact hκ.2.1 ∅ (by simp))
  let ih := rankCollapse_iterand_countable A.order A.top hδ.inaccessible hP hs hz
  let gh := A.rankCollapse_generic hδ.inaccessible hP hs hH
  let T := TwoStepModel.iterandContext A ih gh
  have ht : T = woodinCollapseContext hκ (A.check δ) H hH :=
    A.rankCollapse_iterandContext_eq hδ.inaccessible hP hs hz hH hκ
  have hd := A.rankCollapse_combined_dependentChoiceAt hδ hP hR hκδ hs hz hκ hDC hH
  have he := (TwoStepModel.combinedElementaryMap A ih gh).map_defined dependentChoiceAtFormula
    (fun v ↦ InternalDependentChoiceAt (v 0)) (fun v ↦ InternalDependentChoiceAt (v 0))
    ![(A.rankCollapseCombinedContext hδ.inaccessible hP hs hz hH).check κ]
  have hu : InternalDependentChoiceAt (T.check (A.check κ)) := by
    have hh := he.mp hd
    change InternalDependentChoiceAt (TwoStepModel.combinedEquiv A ih gh
      ((A.rankCollapseCombinedContext hδ.inaccessible hP hs hz hH).check κ)) at hh
    exact TwoStepModel.combinedEquiv_check A ih gh κ ▸ hh
  rwa [ht] at hu

theorem rankCollapse_tail_dependentChoiceBelow :
    ∀ η ∈ (woodinCollapseContext hκ (A.check δ) H hH).check (A.check δ), InternalDependentChoiceAt η := by
  let T := woodinCollapseContext hκ (A.check δ) H hH
  let := hδ.1.1
  let := hκ.1.1
  intro η hη
  obtain ⟨α, hα, rfl⟩ := (T.mem_check_iff (A.check δ) η).mp hη
  let := IsOrdinal.of_mem hα
  exact (A.rankCollapse_tail_dependentChoiceAt hδ hP hR hκδ hκ hDC hH).of_cardLE
    (WoodinCollapseModel.check_ordinal_cardLE hκ (A.check_regular_of_small hδ.inaccessible hP) hα hH)

theorem rankCollapse_combined_dependentChoiceBelow (hs : κ ⊆ δ) (hz : (∅ : V) ∈ κ) :
    ∀ η ∈ (A.rankCollapseCombinedContext hδ.inaccessible hP hs hz hH).check δ, InternalDependentChoiceAt η := by
  let ih := rankCollapse_iterand_countable A.order A.top hδ.inaccessible hP hs hz
  let gh := A.rankCollapse_generic hδ.inaccessible hP hs hH
  let T := TwoStepModel.iterandContext A ih gh
  have ht : T = woodinCollapseContext hκ (A.check δ) H hH :=
    A.rankCollapse_iterandContext_eq hδ.inaccessible hP hs hz hH hκ
  have hu : ∀ η ∈ T.check (A.check δ), InternalDependentChoiceAt η := by
    rw [ht]
    exact A.rankCollapse_tail_dependentChoiceBelow hδ hP hR hκδ hκ hDC hH
  have he := (TwoStepModel.combinedElementaryMap A ih gh).map_defined dependentChoiceBelowFormula
    (fun v ↦ ∀ η ∈ v 0, InternalDependentChoiceAt η)
    (fun v ↦ ∀ η ∈ v 0, InternalDependentChoiceAt η)
    ![(A.rankCollapseCombinedContext hδ.inaccessible hP hs hz hH).check δ]
  apply he.mpr
  change ∀ η ∈ TwoStepModel.combinedEquiv A ih gh
    ((A.rankCollapseCombinedContext hδ.inaccessible hP hs hz hH).check δ), InternalDependentChoiceAt η
  exact (TwoStepModel.combinedEquiv_check A ih gh δ).symm ▸ hu

end ForcingContext
end ZFVP
