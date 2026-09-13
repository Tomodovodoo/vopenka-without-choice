import ZFVP.ModelTheory.ClassForcingTowerBoundedModels
import ZFVP.ModelTheory.ForcingDependentChoiceTransfer
import ZFVP.ModelTheory.ClassForcingBoundedReduction
import ZFVP.ModelTheory.QuotientOrderReflectingClosure
import ZFVP.ModelTheory.QuotientSectionSeparative
import ZFVP.ModelTheory.ClassForcingTowerSplitProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

noncomputable def boundedQuotient (A : ForcingContext V) (i j : V) : A.Model :=
  A.projectionQuotient (T.boundedConditions j) (T.boundedProjection i j)

noncomputable def boundedQuotientOrder (A : ForcingContext V) (i j : V) : A.Model :=
  A.projectionQuotientOrder (T.boundedConditions j) (T.boundedOrder j) (T.boundedProjection i j)

theorem check_mem_boundedQuotient_iff (A : ForcingContext V) {i j c : V}
    [IsOrdinal i] [IsOrdinal j] (hP : A.P = T.P i) :
    A.check c ∈ T.boundedQuotient A i j ↔
      c ∈ T.boundedConditions j ∧ T.projectCondition i c ∈ A.G := by
  have hm : T.boundedProjection i j ∈ A.P ^ T.boundedConditions j := by
    rw [hP]
    exact T.boundedProjection_maps i j
  rw [boundedQuotient, A.check_mem_projectionQuotient_iff hm]
  constructor
  · rintro ⟨hc, hg⟩
    exact ⟨hc, (T.boundedProjection_value hc) ▸ hg⟩
  · rintro ⟨hc, hg⟩
    exact ⟨hc, (T.boundedProjection_value hc).symm ▸ hg⟩

theorem boundedQuotient_mono (A : ForcingContext V) {i j K : V}
    [IsOrdinal i] [IsOrdinal j] [IsOrdinal K] (hP : A.P = T.P i)
    (hjK : j ⊆ K) : T.boundedQuotient A i j ⊆ T.boundedQuotient A i K := by
  intro x hx
  have hm : T.boundedProjection i j ∈ A.P ^ T.boundedConditions j := by
    rw [hP]
    exact T.boundedProjection_maps i j
  obtain ⟨c, _, _, rfl⟩ := (A.mem_projectionQuotient_iff hm x).mp hx
  obtain ⟨hc, hg⟩ := (T.check_mem_boundedQuotient_iff A hP).mp hx
  exact (T.check_mem_boundedQuotient_iff A hP).mpr ⟨T.boundedConditions_mono hjK _ hc, hg⟩

theorem boundedQuotient_reduce_mem (A : ForcingContext V) {i j c : V}
    [IsOrdinal i] [IsOrdinal j] (hP : A.P = T.P i) (hij : i ⊆ j)
    (hc : c ∈ T.boundedConditions j) (hg : A.check c ∈ T.boundedQuotient A i j) :
    A.check (T.reduceCondition j c) ∈ A.projectionQuotient (T.P j) (T.projection i j) := by
  have hm : T.projection i j ∈ A.P ^ T.P j := by
    rw [hP]
    exact T.projection_function i j inferInstance inferInstance hij
  apply (A.check_mem_projectionQuotient_iff hm).mpr
  refine ⟨T.reduceCondition_mem hc, ?_⟩
  rw [T.boundedProjection_reduce hij hc]
  exact ((T.check_mem_boundedQuotient_iff A hP).mp hg).2


theorem boundedReduction_commutes {i j : V} [IsOrdinal i] [IsOrdinal j]
    (hij : i ⊆ j) : ∀ c ∈ T.boundedConditions j,
      (T.projection i j) ‘ ((T.boundedReduction j) ‘ c) = (T.boundedProjection i j) ‘ c := by
  intro c hc
  rw [T.boundedReduction_value hc, T.boundedProjection_value hc]
  exact T.boundedProjection_reduce hij hc

theorem boundedQuotient_checked_separative_iff (A : ForcingContext V) {i j c d : V}
    [IsOrdinal i] [IsOrdinal j] (hP : A.P = T.P i) (hij : i ⊆ j)
    (hc : c ∈ T.boundedConditions j) (hd : d ∈ T.boundedConditions j)
    (hcG : A.check c ∈ T.boundedQuotient A i j) (hdG : A.check d ∈ T.boundedQuotient A i j) :
    ⟨A.check c, A.check d⟩ₖ ∈ forcingSeparativeOrder
      (T.boundedQuotient A i j) (T.boundedQuotientOrder A i j) ↔
    ⟨A.check (T.reduceCondition j c), A.check (T.reduceCondition j d)⟩ₖ ∈
      forcingSeparativeOrder (A.projectionQuotient (T.P j) (T.projection i j))
        (A.projectionQuotientOrder (T.P j) (T.R j) (T.projection i j)) := by
  have hm : T.boundedProjection i j ∈ A.P ^ T.boundedConditions j := by
    rw [hP]; exact T.boundedProjection_maps i j
  have hτ : T.projection i j ∈ A.P ^ T.P j := by
    rw [hP]; exact T.projection_function i j inferInstance inferInstance hij
  have hh := A.projectionQuotient_checked_separative_iff_of_order_reflecting hm hτ
    (T.boundedReduction_splitProjection j) (T.boundedReduction_commutes hij)
    (fun a ha b hb ↦ T.boundedReduction_order_iff ha hb) hc hd hcG hdG
  simpa only [boundedQuotient, boundedQuotientOrder, T.boundedReduction_value hc, T.boundedReduction_value hd] using hh

theorem boundedQuotient_separative_closedAt_iff (A : ForcingContext V) {i j : V}
    [IsOrdinal i] [IsOrdinal j] (hP : A.P = T.P i) (hij : i ⊆ j)
    {α : A.Model} [IsOrdinal α] :
    IsForcingClosedAt (T.boundedQuotient A i j)
      (forcingSeparativeOrder (T.boundedQuotient A i j) (T.boundedQuotientOrder A i j)) α ↔
    IsForcingClosedAt (A.projectionQuotient (T.P j) (T.projection i j))
      (forcingSeparativeOrder (A.projectionQuotient (T.P j) (T.projection i j))
        (A.projectionQuotientOrder (T.P j) (T.R j) (T.projection i j))) α := by
  have hm : T.boundedProjection i j ∈ A.P ^ T.boundedConditions j := by
    rw [hP]; exact T.boundedProjection_maps i j
  have hτ : T.projection i j ∈ A.P ^ T.P j := by
    rw [hP]; exact T.projection_function i j inferInstance inferInstance hij
  exact A.projectionQuotient_separative_closedAt_iff_of_order_reflecting hm hτ
    (T.boundedReduction_splitProjection j) (T.boundedReduction_commutes hij)
    (fun a ha b hb ↦ T.boundedReduction_order_iff ha hb)


theorem boundedQuotient_checked_separative_coherent (A : ForcingContext V) {i j K c d : V}
    [IsOrdinal i] [IsOrdinal j] [IsOrdinal K] (hP : A.P = T.P i)
    (hij : i ⊆ j) (hjK : j ⊆ K)
    (hc : c ∈ T.boundedConditions j) (hd : d ∈ T.boundedConditions j)
    (hcG : A.check c ∈ T.boundedQuotient A i j) (hdG : A.check d ∈ T.boundedQuotient A i j) :
    ⟨A.check c, A.check d⟩ₖ ∈ forcingSeparativeOrder
      (T.boundedQuotient A i K) (T.boundedQuotientOrder A i K) ↔
    ⟨A.check c, A.check d⟩ₖ ∈ forcingSeparativeOrder
      (T.boundedQuotient A i j) (T.boundedQuotientOrder A i j) := by
  have hiK := subset_trans hij hjK
  have hcK := T.boundedConditions_mono hjK _ hc
  have hdK := T.boundedConditions_mono hjK _ hd
  have hcGK := T.boundedQuotient_mono A hP hjK _ hcG
  have hdGK := T.boundedQuotient_mono A hP hjK _ hdG
  have houter := T.boundedQuotient_checked_separative_iff A hP hiK hcK hdK hcGK hdGK
  rw [T.reduceCondition_stage hjK hc, T.reduceCondition_stage hjK hd] at houter
  have hπ : T.projection i K ∈ A.P ^ T.P K := by
    rw [hP]; exact T.projection_function i K inferInstance inferInstance hiK
  have hτ : T.projection i j ∈ A.P ^ T.P j := by
    rw [hP]; exact T.projection_function i j inferInstance inferInstance hij
  have hsection := A.projectionQuotient_section_separative_iff hπ hτ (T.splitProjection hjK)
    (T.projection_comp i j K inferInstance inferInstance inferInstance hij hjK)
    (T.reduceCondition_mem hc) (T.reduceCondition_mem hd)
    (T.boundedQuotient_reduce_mem A hP hij hc hcG) (T.boundedQuotient_reduce_mem A hP hij hd hdG)
  exact houter.trans (hsection.trans (T.boundedQuotient_checked_separative_iff A hP hij hc hd hcG hdG).symm)

theorem boundedQuotient_separative_coherent (A : ForcingContext V) {i j K : V}
    [IsOrdinal i] [IsOrdinal j] [IsOrdinal K] (hP : A.P = T.P i)
    (hij : i ⊆ j) (hjK : j ⊆ K) :
    ∀ x ∈ T.boundedQuotient A i j, ∀ y ∈ T.boundedQuotient A i j,
      ⟨x, y⟩ₖ ∈ forcingSeparativeOrder (T.boundedQuotient A i K) (T.boundedQuotientOrder A i K) ↔
      ⟨x, y⟩ₖ ∈ forcingSeparativeOrder (T.boundedQuotient A i j) (T.boundedQuotientOrder A i j) := by
  intro x hx y hy
  have hm : T.boundedProjection i j ∈ A.P ^ T.boundedConditions j := by
    rw [hP]; exact T.boundedProjection_maps i j
  obtain ⟨c, hc, _, rfl⟩ := (A.mem_projectionQuotient_iff hm x).mp hx
  obtain ⟨d, hd, _, rfl⟩ := (A.mem_projectionQuotient_iff hm y).mp hy
  exact T.boundedQuotient_checked_separative_coherent A hP hij hjK hc hd hx hy

/-- Ordinary quotient closure supplies closure of every bounded tagged carrier
with the separative order of one fixed, larger bounded quotient. -/
theorem boundedQuotient_closedAt_ambient (A : ForcingContext V) {i j K : V}
    [IsOrdinal i] [IsOrdinal j] [IsOrdinal K] (hP : A.P = T.P i)
    (hij : i ⊆ j) (hjK : j ⊆ K) {α : A.Model} [IsOrdinal α]
    (hclosed : IsForcingClosedAt (A.projectionQuotient (T.P j) (T.projection i j))
      (forcingSeparativeOrder (A.projectionQuotient (T.P j) (T.projection i j))
        (A.projectionQuotientOrder (T.P j) (T.R j) (T.projection i j))) α) :
    IsForcingClosedAt (T.boundedQuotient A i j)
      (forcingSeparativeOrder (T.boundedQuotient A i K) (T.boundedQuotientOrder A i K)) α :=
  forcingClosedAt_of_order_agreement (T.boundedQuotient_separative_coherent A hP hij hjK)
    ((T.boundedQuotient_separative_closedAt_iff A hP hij).mpr hclosed)

theorem boundedQuotient_closedThrough_ambient (A : ForcingContext V) {i j K : V}
    [IsOrdinal i] [IsOrdinal j] [IsOrdinal K] (hP : A.P = T.P i)
    (hij : i ⊆ j) (hjK : j ⊆ K) {α : A.Model}
    (hclosed : IsForcingClosedThrough (A.projectionQuotient (T.P j) (T.projection i j))
      (forcingSeparativeOrder (A.projectionQuotient (T.P j) (T.projection i j))
        (A.projectionQuotientOrder (T.P j) (T.R j) (T.projection i j))) α) :
    IsForcingClosedThrough (T.boundedQuotient A i j)
      (forcingSeparativeOrder (T.boundedQuotient A i K) (T.boundedQuotientOrder A i K)) α := by
  intro β hβ hβα
  let := hβ
  exact T.boundedQuotient_closedAt_ambient A hP hij hjK (hclosed β hβ hβα)

end DefinableForcingTower
end ZFVP
