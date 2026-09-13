import ZFVP.ModelTheory.SparseOrderCoordinates
import ZFVP.ModelTheory.WoodinSparseCoordinateNames
import ZFVP.ModelTheory.WoodinSparseAllRestrictions
import ZFVP.ModelTheory.WoodinSparseCutDictionary

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ p q : V} [IsOrdinal θ]
local notation "P" => (forcingCodeP (woodinSparseStageCode θ)) ‘ θ
local notation "R" => (forcingCodeR (woodinSparseStageCode θ)) ‘ θ

theorem woodinSparseStageCode_coordinate_comparison_iff
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {a : V} [IsOrdinal a] (hp : p ∈ P) (hq : q ∈ P) :
    SparseCoordinateComparison P R a p q ↔
      p ↾ a ∈ forcingFormula (sparseCarrierCut P a) (sparseCutOrder P R a)
        isSubsetOf (standardTuple ![q ‘ a, p ‘ a]) :=
  sparseSubsetComparison_iff
    (sparseCutOrder_preorder ((woodinSparseStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ)))
    (woodinSparseStageCode_coordinate_isName hΩ hAC hθ hq)
    (woodinSparseStageCode_coordinate_isName hΩ hAC hθ hp)

theorem woodinSparseStageCode_restrict_mem_cut
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {a : V} [IsOrdinal a] (hp : p ∈ P) : p ↾ a ∈ sparseCarrierCut P a := by
  apply mem_sparseCarrierCut_iff.mpr
  refine ⟨woodinSparseStageCode_restrict_any hΩ hAC hθ hp, ?_⟩
  intro x hx
  rw [domain_restrict_eq] at hx
  exact (mem_inter_iff.mp hx).2

theorem woodinSparseStageCode_coordinate_empty
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {a : V} [IsOrdinal a] (hp : p ∈ P)
    (hp0 : p ‘ a = ∅) (hq0 : q ‘ a = ∅) : SparseCoordinateComparison P R a p q := by
  have hf := woodinSparseStageCode_valid hΩ hAC hθ
  have ht := hf.system.tops.top θ (mem_succ_self θ)
  rw [woodinSparseStageCode_top hΩ hAC hθ] at ht
  exact sparseCoordinateComparison_empty (hf.system.order.preorder θ (mem_succ_self θ)) ht
    (woodinSparseStageCode_restrict_mem_cut hΩ hAC hθ hp) hp0 hq0

theorem woodinSparseStageCode_coordinates_restriction
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ succ θ) (hp : p ∈ P) (hq : q ∈ P) :
    SparseOrderCoordinates ((forcingCodeP (woodinSparseStageCode i)) ‘ i)
      ((forcingCodeR (woodinSparseStageCode i)) ‘ i) (succ (woodinSourceIndex i))
      (p ↾ (succ (woodinSourceIndex i))) (q ↾ (succ (woodinSourceIndex i))) ↔
      SparseOrderCoordinates P R (succ (woodinSourceIndex i)) p q := by
  let := IsOrdinal.of_mem hi
  let := (woodinSparseStageCode_sparse hΩ hAC hθ hp).1
  let := (woodinSparseStageCode_sparse hΩ hAC hθ hq).1
  rw [woodinSparseStageCode_carrier_recovery hΩ hAC hθ hi,
    ← woodinSparseStageCode_cut_order_recovery hΩ hAC hθ hi]
  exact sparseOrderCoordinates_restrict (subset_refl _)

end ZFVP
