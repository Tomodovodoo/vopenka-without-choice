import ZFVP.ModelTheory.SaturatedEmptyIterand
import ZFVP.ModelTheory.ForcingCnOneTruth
import ZFVP.ModelTheory.SuccessorRankWoodinCollapse
import ZFVP.ModelTheory.ForcingSmallInaccessible
import ZFVP.SetTheory.TwoStepRankBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def boundedPrefixCollapseName (P R one κ γ θ : V) : V :=
  forcingSaturatedName P R (forcingNameHierarchy P θ)
    (woodinCollapseName P R (checkName one κ) (checkName one γ))

theorem boundedPrefixCollapseName_isName (P R one κ γ θ : V) :
    IsForcingName P (boundedPrefixCollapseName P R one κ γ θ) :=
  forcingSaturatedName_isName _ _ _ _

theorem boundedPrefixCollapseName_mem_hierarchy {P R one κ γ θ δ : V}
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hθ : θ ∈ δ) :
    boundedPrefixCollapseName P R one κ γ θ ∈ hierarchy δ := by
  let := hδ.1
  exact subset_mem_hierarchy_limit hδ.rankCriterion.2.2.1
    (prod_mem_hierarchy_limit hδ.rankCriterion.2.2.1
      (forcingNameHierarchy_mem_hierarchy hδ hP hθ) hP)
    (forcingSaturatedName_subset _ _ _ _)

theorem boundedPrefixCollapse_iterand {P R one κ γ θ : V} [IsOrdinal θ] [IsOrdinal γ]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (h0 : (∅ : V) ∈ θ)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![checkName one κ])) :
    IsForcingIterand P R (boundedPrefixCollapseName P R one κ γ θ)
      (reverseInclusionOrderName P R (boundedPrefixCollapseName P R one κ γ θ)) ∅ :=
  saturatedWoodinCollapse_empty_iterand hR ht
    ⟨checkName one κ, checkName_isName ht.1 κ⟩
    ⟨checkName one γ, checkName_isName ht.1 γ⟩
    ((mem_forcingNameHierarchy P θ ∅).mpr ⟨∅, h0, by simp⟩)
    hκ (fun _ hp ↦ forces_checked_ordinal hR ht inferInstance hp)

theorem boundedPrefixCollapse_twoStep_small {P R one κ γ θ δ : V}
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hθ : θ ∈ δ) :
    twoStepConditions P R (boundedPrefixCollapseName P R one κ γ θ) ∅ ∈ hierarchy δ := by
  let := hδ.1
  exact twoStepConditions_mem_hierarchy_limit hδ.rankCriterion.2.2.1 hP
    (boundedPrefixCollapseName_mem_hierarchy hδ hP hθ)
    (ordinal_mem_hierarchy_iff.mpr (hδ.regular.2.1 ∅ (by simp)))

theorem ForcingContext.boundedPrefixCollapseName_value (A : ForcingContext V)
    {κ γ θ : V} [IsOrdinal κ] [IsOrdinal γ] (hθ : Cn 1 θ)
    (hP : A.P ∈ hierarchy θ) (hκ : κ ∈ θ) (hγ : γ ∈ θ) :
    A.ofName ⟨boundedPrefixCollapseName A.P A.R A.one κ γ θ,
      boundedPrefixCollapseName_isName _ _ _ _ _ _⟩ =
      woodinCollapse (A.check κ) (A.check γ) := by
  let := hθ.ordinal
  let cκ : ForcingName A.P := ⟨checkName A.one κ, checkName_isName A.top.1 κ⟩
  let cγ : ForcingName A.P := ⟨checkName A.one γ, checkName_isName A.top.1 γ⟩
  let : IsOrdinal (A.ofName cγ) := by change IsOrdinal (A.check γ); infer_instance
  have hc : A.ofName (A.collapseName cκ cγ) = woodinCollapse (A.check κ) (A.check γ) :=
    A.collapseName_value_of_ordinal cκ cγ
  have hm := woodinCollapse_mem_hierarchy (A.cn_one_check hθ hP)
    (show IsOrdinal (A.check γ) from inferInstance)
    (ordinal_mem_hierarchy_iff.mpr ((A.check_mem_iff _ _).mpr hκ))
    (ordinal_mem_hierarchy_iff.mpr ((A.check_mem_iff _ _).mpr hγ))
  have hcover : A.ofName (A.collapseName cκ cγ) ⊆ hierarchy (A.check θ) := by
    rw [hc]
    exact fun _ hx ↦ (hierarchy_transitive (A.check θ)).mem_trans hx hm
  exact (A.saturatedName_value_of_hierarchy θ (A.collapseName cκ cγ) hcover).trans hc

end ZFVP
