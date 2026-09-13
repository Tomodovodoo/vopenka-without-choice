import ZFVP.ModelTheory.SaturatedHartogsSuccessor
import ZFVP.SetTheory.TwoStepRankBounds
import ZFVP.ModelTheory.TwoStepRankDCForcingAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eventually_hartogsCollapse_rankDCBelow_forcing_eq_countable [Countable V]
    {δ κ γ P R one : V} (hδ : IsWoodinSupercompact δ) (hP : P ∈ hierarchy δ)
    (hκγ : κ ∈ γ) (hγδ : γ ∈ δ)
    (hγ : IsChoicelessInaccessible γ) (hPγ : P ∈ hierarchy γ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![hartogsNumberName P R (checkName one κ)])) :
    ∃ β ∈ δ, γ ∈ β ∧ ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
      let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
      let q := woodinCollapse (hartogsNumber (A.check κ)) (A.check γ)
      let s := woodinCollapseOrder (hartogsNumber (A.check κ)) (A.check γ)
      ∀ ξ : A.Model, A.check β ∈ ξ → IsChoicelessInaccessible ξ → q ∈ hierarchy ξ →
        checkName ∅ (A.check γ) ∈ hierarchy ξ →
        classForcingFormula q s (IsLowRankForcingName q ξ) (by definability)
          dependentChoiceBelowFormula (standardTuple ![checkName ∅ (A.check γ)]) =
        forcingFormula q s dependentChoiceBelowFormula
          (standardTuple ![checkName ∅ (A.check γ)]) := by
  let := hδ.1.1
  let := hγ.1
  let Q := saturatedWoodinCollapseName P R γ
    (hartogsNumberName P R (checkName one κ)) (checkName one γ)
  have hQ : Q ∈ hierarchy δ :=
    subset_mem_hierarchy_limit hδ.inaccessible.rankCriterion.2.2.1
      (prod_mem_hierarchy_limit hδ.inaccessible.rankCriterion.2.2.1
        (forcingNameHierarchy_mem_hierarchy hδ.inaccessible hP hγδ) hP)
      (forcingSaturatedName_subset _ _ _ _)
  have hC : twoStepConditions P R Q ∅ ∈ hierarchy δ :=
    twoStepConditions_mem_hierarchy_limit hδ.inaccessible.rankCriterion.2.2.1 hP hQ
      (ordinal_mem_hierarchy_iff.mpr (hδ.inaccessible.regular.2.1 ∅ (by simp)))
  let h := saturatedHartogsCollapse_iterand hR ht hγ hκ
  obtain ⟨β, hβ, hγβ, hall⟩ := eventually_twoStep_rankDCBelow_forcing_eq_countable hδ
    hC hγδ hR ht h
  refine ⟨β, hβ, hγβ, ?_⟩
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  have hp := A.saturatedHartogsCollapseName_value hγ hPγ hκγ
  change A.ofName ⟨Q, h.posetName⟩ =
    woodinCollapse (hartogsNumber (A.check κ)) (A.check γ) at hp
  have hs : A.ofName ⟨reverseInclusionOrderName P R (Q),
      h.orderName⟩ = woodinCollapseOrder (hartogsNumber (A.check κ)) (A.check γ) := by
    change A.ofName (A.reverseOrderName ⟨Q, h.posetName⟩) = _
    rw [A.reverseOrderName_value, hp]
    rfl
  have ho : A.ofName ⟨∅, h.topName⟩ = ∅ := by
    apply mem_ext
    intro x
    rw [A.mem_ofName_iff]
    simp
  have hh := hall G hG
  change ∀ ξ : A.Model, A.check β ∈ ξ → IsChoicelessInaccessible ξ →
    A.ofName ⟨Q, h.posetName⟩ ∈ hierarchy ξ →
    checkName (A.ofName ⟨∅, h.topName⟩) (A.check γ) ∈ hierarchy ξ →
    classForcingFormula _ _ (IsLowRankForcingName _ ξ) (by definability)
      dependentChoiceBelowFormula (standardTuple ![checkName (A.ofName ⟨∅, h.topName⟩) (A.check γ)]) =
    forcingFormula _ _ dependentChoiceBelowFormula
      (standardTuple ![checkName (A.ofName ⟨∅, h.topName⟩) (A.check γ)]) at hh
  dsimp only [A, Q] at hp hs ho hh
  simpa only [hp, hs, ho] using hh

end ZFVP
