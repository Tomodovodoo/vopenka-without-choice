import ZFVP.ModelTheory.RankCollapseCombinedContext
import ZFVP.ModelTheory.SuccessorRankTwoStep
import ZFVP.ModelTheory.SuccessorRankLiftDC

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankFormulaName_mem_hierarchy {ρ P R δ : V} (hρ : Cn 1 ρ)
    (hP : P ∈ hierarchy ρ) (hδ : IsOrdinal δ) (hδρ : δ ∈ hierarchy ρ)
    {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V) :
    rankFormulaName P R δ φ v ∈ hierarchy ρ := by
  let := hρ.ordinal
  exact subset_mem_hierarchy_limit hρ.successor_closed (rankUniverseName_mem hρ hP hδ hδρ)
    (show rankFormulaName P R δ φ v ⊆ rankUniverseName P δ from sep_subset)

theorem rankCollapse_twoStep_images [Countable V] {ρ γ e c δ P R one κ : V}
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hc : IsCriticalPoint (hierarchy (succ ρ)) e c) (hcρ : c ∈ ρ)
    (hci : IsChoicelessInaccessible c) (hδ : IsChoicelessInaccessible δ)
    (hP : P ∈ hierarchy c) (hR : R ∈ hierarchy c)
    (hord : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hκ : κ ∈ c) (hz : (∅ : V) ∈ κ) (hec : e ‘ c = δ) :
    e ‘ (twoStepConditions P R (rankCollapseName P R one κ c) ∅) =
        twoStepConditions P R (rankCollapseName P R one κ δ) ∅ ∧
      e ‘ (twoStepOrder P R (rankCollapseName P R one κ c)
        (rankOrderName P R c (rankCollapseName P R one κ c)) ∅) =
        twoStepOrder P R (rankCollapseName P R one κ δ)
          (rankOrderName P R δ (rankCollapseName P R one κ δ)) ∅ := by
  let := hρ.ordinal
  let := hci.1
  let := hδ.1
  let := hγ.ordinal
  let := hierarchy_transitive (succ ρ)
  let := hierarchy_transitive (succ γ)
  let := IsOrdinal.of_mem hκ
  have hfix := successorRankEmbedding_fixed_below_criticalPoint hρ hγ he hc hcρ
  have hcV : c ∈ hierarchy ρ := ordinal_mem_hierarchy_iff.mpr hcρ
  have hinc : hierarchy c ⊆ hierarchy ρ := hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hcρ)
  have hPl := hinc P hP
  have hRl := hinc R hR
  have h0c : (∅ : V) ∈ hierarchy c := ordinal_mem_hierarchy_iff.mpr
    (IsOrdinal.toIsTransitive.mem_trans hz hκ)
  have h0 := hinc ∅ h0c
  have heP := hfix P hP
  have heR := hfix R hR
  have heone := hfix one ((hierarchy_transitive c).mem_trans htop.1 hP)
  have heκ := hc.fixed_below hκ
  have he0 := hfix ∅ h0c
  have hcδ : c ⊆ δ := IsOrdinal.toIsTransitive.transitive _ (hec ▸ hc.lt_value he)
  have hκc : κ ⊆ c := IsOrdinal.toIsTransitive.transitive _ hκ
  have hord' : IsForcingPreorder (e ‘ P) (e ‘ R) := by rwa [heP, heR]
  have hQ : rankCollapseName P R one κ c ∈ hierarchy ρ := rankFormulaName_mem_hierarchy (R := R) hρ hPl hci.1 hcV
    sigmaOneWoodinConditionFormula ![checkName one κ, checkName one c, rankUniverseName P c]
  have hS : rankOrderName P R c (rankCollapseName P R one κ c) ∈ hierarchy ρ := rankFormulaName_mem_hierarchy (R := R) hρ hPl hci.1 hcV
    boundedOrderRowFormula ![rankCollapseName P R one κ c]
  have heQ := successorRankEmbedding_value_rankCollapseName hρ hγ he hPl hRl htop.1
    ((hierarchy_transitive ρ).mem_trans hκ hcV) hci.1 hcV hord hord'
  rw [heP, heR, heone, heκ, hec] at heQ
  have heS := successorRankEmbedding_value_rankOrderName hρ hγ he hPl hRl hci.1 hcV hord hord'
    hQ (rankCollapseName_isName _ _ _ _ _)
  rw [heP, heR, hec, heQ] at heS
  have hi := rankCollapse_iterand_countable hord htop hci hP hκc hz
  have hi' := rankCollapse_iterand_countable hord htop hδ (hierarchy_mono hcδ P hP)
    (subset_trans hκc hcδ) hz
  have hei : IsForcingIterand (e ‘ P) (e ‘ R) (e ‘ (rankCollapseName P R one κ c))
      (e ‘ (rankOrderName P R c (rankCollapseName P R one κ c))) (e ‘ (∅ : V)) := by
    rwa [heP, heR, heQ, heS, he0]
  constructor
  · have hh := successorRankEmbedding_value_twoStepConditions hρ hγ he hPl hRl hQ h0 hi.posetName
    simpa only [heP, heR, heQ, he0] using hh
  · have hh := successorRankEmbedding_value_twoStepOrder hρ hγ he hPl hRl hQ hS h0 hord hord' hi hei
    simpa only [heP, heR, heQ, heS, he0] using hh

namespace ForcingContext
variable (A : ForcingContext V)

theorem rankCollapse_successorRankLift [Countable V] {ρ γ e c δ κ : V}
    [IsOrdinal c] [IsOrdinal δ]
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hc : IsCriticalPoint (hierarchy (succ ρ)) e c) (hcρ : c ∈ ρ)
    (hci : IsChoicelessInaccessible c) (hδ : IsChoicelessInaccessible δ)
    (hP : A.P ∈ hierarchy c) (hR : A.R ∈ hierarchy c)
    (hκ : κ ∈ c) (hκc : κ ⊆ c) (hcδ : c ⊆ δ) (hz : (∅ : V) ∈ κ) (hec : e ‘ c = δ)
    {Hc Hδ : Set A.Model}
    (hHc : IsExternalForcingGeneric (woodinCollapse (A.check κ) (A.check c))
      (woodinCollapseOrder (A.check κ) (A.check c)) Hc)
    (hHδ : IsExternalForcingGeneric (woodinCollapse (A.check κ) (A.check δ))
      (woodinCollapseOrder (A.check κ) (A.check δ)) Hδ)
    (hH : ∀ x, x ∈ Hc ↔ x ∈ Hδ ∧ x ∈ woodinCollapse (A.check κ) (A.check c)) :
    SuccessorRankLiftData (A.rankCollapseCombinedContext hci hP hκc hz hHc)
      (A.rankCollapseCombinedContext hδ (hierarchy_mono hcδ A.P hP)
        (subset_trans hκc hcδ) hz hHδ) ρ γ e := by
  let := hρ.ordinal
  let := hci.1
  let := hδ.1
  have hcV : c ∈ hierarchy ρ := ordinal_mem_hierarchy_iff.mpr hcρ
  have hPl := hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hcρ) A.P hP
  have hQ : rankCollapseName A.P A.R A.one κ c ∈ hierarchy ρ :=
    rankFormulaName_mem_hierarchy hρ hPl hci.1 hcV _ _
  have h0 : (∅ : V) ∈ hierarchy ρ := (hierarchy_transitive ρ).mem_trans
    (IsOrdinal.toIsTransitive.mem_trans hz hκ) hcV
  have him := rankCollapse_twoStep_images hρ hγ he hc hcρ hci hδ hP hR A.order A.top hκ hz hec
  refine ⟨hρ, hγ, he, twoStepConditions_mem_hierarchy hρ hPl hQ h0,
    twoStepOrder_mem_hierarchy hρ hPl hQ h0, him.1, him.2, ?_⟩
  intro z hzG
  have hzC := (A.rankCollapseCombinedContext hci hP hκc hz hHc).generic.1.1 z hzG
  change z ∈ twoStepConditions A.P A.R (rankCollapseName A.P A.R A.one κ c) ∅ at hzC
  rw [successorRankEmbedding_fixes_rankCollapse_conditions hρ hγ he hc hcρ hci hP z hzC]
  have hm := twoStepCombinedFilter_restrict A (rankCollapseName_isName A.P A.R A.one κ c)
    (rankCollapseName_mono_countable A.order A.top hci hδ hP hκc hcδ)
    (H := Hc) (H' := Hδ) (t := (∅ : V)) (fun x ↦ by
      change x ∈ Hc ↔ x ∈ Hδ ∧ x ∈ A.ofName (A.rankCollapse κ c)
      rw [A.rankCollapse_value hci hP hκc]
      exact hH x) z
  exact (hm.mp hzG).1

theorem rankCollapse_dependentChoiceBelow_iff [Countable V] {ρ γ e c δ κ : V}
    [IsOrdinal c] [IsOrdinal δ]
    (hSC : IsWoodinSupercompact δ) (hρ : IsSigmaOneStarCorrect ρ) (hγ : IsSigmaOneStarCorrect γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hc : IsCriticalPoint (hierarchy (succ ρ)) e c) (hcρ : c ∈ ρ)
    (hci : IsChoicelessInaccessible c)
    (hP : A.P ∈ hierarchy c) (hR : A.R ∈ hierarchy c)
    (hκ : κ ∈ c) (hκc : κ ⊆ c) (hcδ : c ⊆ δ) (hz : (∅ : V) ∈ κ) (hec : e ‘ c = δ)
    {Hc Hδ : Set A.Model}
    (hHc : IsExternalForcingGeneric (woodinCollapse (A.check κ) (A.check c))
      (woodinCollapseOrder (A.check κ) (A.check c)) Hc)
    (hHδ : IsExternalForcingGeneric (woodinCollapse (A.check κ) (A.check δ))
      (woodinCollapseOrder (A.check κ) (A.check δ)) Hδ)
    (hH : ∀ x, x ∈ Hc ↔ x ∈ Hδ ∧ x ∈ woodinCollapse (A.check κ) (A.check c)) :
    let Bc := A.rankCollapseCombinedContext hci hP hκc hz hHc
    let Bδ := A.rankCollapseCombinedContext hSC.inaccessible (hierarchy_mono hcδ A.P hP)
      (subset_trans hκc hcδ) hz hHδ
    (∀ η ∈ Bc.check c, InternalDependentChoiceAt η) ↔
      ∀ η ∈ Bδ.check δ, InternalDependentChoiceAt η := by
  dsimp only
  let Bc := A.rankCollapseCombinedContext hci hP hκc hz hHc
  let Bδ := A.rankCollapseCombinedContext hSC.inaccessible (hierarchy_mono hcδ A.P hP)
    (subset_trans hκc hcδ) hz hHδ
  have L : SuccessorRankLiftData Bc Bδ ρ γ e :=
    A.rankCollapse_successorRankLift hρ.1 hγ.1 he hc hcρ hci hSC.inaccessible hP hR
      hκ hκc hcδ hz hec hHc hHδ hH
  have heone : e ‘ Bc.one = Bδ.one := by
    change e ‘ ⟨A.one, (∅ : V)⟩ₖ = ⟨A.one, (∅ : V)⟩ₖ
    apply successorRankEmbedding_fixed_below_criticalPoint hρ.1 hγ.1 he hc hcρ
    exact kpair_mem_hierarchy_limit hci.rankCriterion.2.2.1
      ((hierarchy_transitive c).mem_trans A.top.1 hP)
      (ordinal_mem_hierarchy_iff.mpr (IsOrdinal.toIsTransitive.mem_trans hz hκ))
  have hh := L.dependentChoiceBelow_iff (κ := c) (α := succ c) hSC hρ hγ heone
    (hρ.1.successor_closed c hcρ) (mem_succ_iff.mpr (Or.inl rfl))
  rw [hec] at hh
  exact hh

end ForcingContext
end ZFVP
