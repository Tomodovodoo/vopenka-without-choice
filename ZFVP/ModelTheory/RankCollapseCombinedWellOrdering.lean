import ZFVP.ModelTheory.RankCollapseCombinedContext
import ZFVP.ModelTheory.TwoStepEquivalence
import ZFVP.ModelTheory.WoodinCollapseLiftDomain
import ZFVP.ModelTheory.ForcingCnOneTruth
import ZFVP.SetTheory.CardinalDictionary

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]

namespace ForcingContext
variable (A : ForcingContext V) {κ δ : V}
  (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ)
  (hκδ : κ ⊆ δ) (hz : (∅ : V) ∈ κ) {H : Set A.Model}
  (hH : IsExternalForcingGeneric (woodinCollapse (A.check κ) (A.check δ))
    (woodinCollapseOrder (A.check κ) (A.check δ)) H)

theorem rankCollapse_iterandContext_eq (hκ : IsRegularCardinal (A.check κ)) :
    TwoStepModel.iterandContext A (rankCollapse_iterand_countable A.order A.top hδ hP hκδ hz)
      (A.rankCollapse_generic hδ hP hκδ hH) = woodinCollapseContext hκ (A.check δ) H hH := by
  unfold TwoStepModel.iterandContext woodinCollapseContext
  congr 1
  · exact A.rankCollapse_value hδ hP hκδ
  · exact A.rankCollapseOrder_value hδ hP hκδ
  · apply mem_ext
    intro x
    rw [A.mem_ofName_iff]
    simp

theorem rankCollapse_combined_check_hierarchy_wellOrderable
    (hκ : IsRegularCardinal (A.check κ)) {ρ : V} (hρ : Cn 1 ρ)
    (hPρ : A.P ∈ hierarchy ρ) (hρδ : ρ ∈ δ) :
    IsWellOrderable ((A.rankCollapseCombinedContext hδ hP hκδ hz hH).check (hierarchy ρ)) := by
  let := hδ.1
  let := hρ.ordinal
  let ih := rankCollapse_iterand_countable A.order A.top hδ hP hκδ hz
  let gh := A.rankCollapse_generic hδ hP hκδ hH
  let T := TwoStepModel.iterandContext A ih gh
  have ht : T = woodinCollapseContext hκ (A.check δ) H hH :=
    A.rankCollapse_iterandContext_eq hδ hP hκδ hz hH hκ
  have hw : IsWellOrderable (T.check (hierarchy (A.check ρ))) := by
    rw [ht]
    exact WoodinCollapseModel.check_hierarchy_wellOrderable hκ hH (A.cn_one_check hρ hPρ)
      ((A.check_mem_iff _ _).mpr hρδ)
  have hs : A.check (hierarchy ρ) ⊆ hierarchy (A.check ρ) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (A.mem_check_iff _ x).mp hx
    exact A.ofName_mem_checked_hierarchy ⟨checkName A.one a, checkName_isName A.top.1 a⟩
      (hρ.checkName_closed ((hierarchy_transitive ρ).mem_trans A.top.1 hPρ) ha)
  have hw' : IsWellOrderable (T.check (A.check (hierarchy ρ))) :=
    wellOrderable_of_cardLE (cardLE_of_subset ((T.checkEmbedding.subset_iff _ _).mpr hs)) hw
  apply ((TwoStepModel.combinedElementaryMap A ih gh).map_wellOrderable_iff _).mp
  change IsWellOrderable (TwoStepModel.combinedEquiv A ih gh
    ((A.rankCollapseCombinedContext hδ hP hκδ hz hH).check (hierarchy ρ)))
  exact (TwoStepModel.combinedEquiv_check A ih gh (hierarchy ρ)).symm ▸ hw'

theorem rankCollapse_combined_lowerName_wellOrderable
    (hκ : IsRegularCardinal (A.check κ)) {ρ : V} (hρ : Cn 1 ρ)
    (hPρ : A.P ∈ hierarchy ρ) (hρδ : ρ ∈ δ)
    (τ : ForcingName (A.rankCollapseCombinedContext hδ hP hκδ hz hH).P)
    (hτ : τ.val ∈ hierarchy ρ) :
    IsWellOrderable ((A.rankCollapseCombinedContext hδ hP hκδ hz hH).ofName τ) := by
  let B := A.rankCollapseCombinedContext hδ hP hκδ hz hH
  let := hρ.ordinal
  have hs : nameClosure τ.val ⊆ hierarchy ρ :=
    nameClosure_minimal (transitive_subnameClosed (hierarchy_transitive ρ)) hτ
  apply B.ofName_wellOrderable_of_closure τ
  exact wellOrderable_of_cardLE (cardLE_of_subset ((B.checkEmbedding.subset_iff _ _).mpr hs))
    (A.rankCollapse_combined_check_hierarchy_wellOrderable hδ hP hκδ hz hH hκ hρ hPρ hρδ)

end ForcingContext
end ZFVP
