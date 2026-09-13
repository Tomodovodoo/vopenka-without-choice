import ZFVP.ModelTheory.ForcingFormulaNameRank
import ZFVP.ModelTheory.ForcingRankCollapseOrder
import ZFVP.ModelTheory.WoodinPrefixNameFormulas

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]

theorem woodinPrefixPosetName_mem_hierarchy_countable {P R one κ δ θ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκ : κ ⊆ δ)
    (hθ : IsChoicelessInaccessible θ) (hδθ : δ ∈ θ) :
    woodinPrefixPosetName P R one κ δ ∈ hierarchy θ := by
  let := hδ.1
  let := hθ.1
  let cκ : ForcingName P := ⟨checkName one κ, checkName_isName htop.1 κ⟩
  let cδ : ForcingName P := ⟨checkName one δ, checkName_isName htop.1 δ⟩
  let ν : ForcingName P := ⟨rankCollapseName P R one κ δ, rankCollapseName_isName _ _ _ _ _⟩
  have hν : ν.val ∈ hierarchy θ := subset_mem_hierarchy_limit hθ.rankCriterion.2.2.1
    (hierarchy_mem hδθ) (rankFormulaName_subset hδ.rankCriterion.2.2.1 hP _ _)
  apply formulaUniqueName_mem_hierarchy_of_semantics hR htop hθ.rankCriterion.2.2.1
    (hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hδθ) P hP)
    totalWoodinCollapseFormula ![cκ, cδ] ν hν
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  apply (Defined.eval_iff _).mpr
  change A.ofName ν = totalWoodinCollapse (A.check κ) (A.check δ)
  rw [totalWoodinCollapse_eq]
  exact A.rankCollapse_value hδ hP hκ

theorem woodinPrefixOrderName_mem_hierarchy_countable {P R one κ δ θ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκ : κ ⊆ δ)
    (hθ : IsChoicelessInaccessible θ) (hδθ : δ ∈ θ) :
    woodinPrefixOrderName P R one κ δ ∈ hierarchy θ := by
  let := hδ.1
  let := hθ.1
  let cκ : ForcingName P := ⟨checkName one κ, checkName_isName htop.1 κ⟩
  let cδ : ForcingName P := ⟨checkName one δ, checkName_isName htop.1 δ⟩
  let Q : ForcingName P := ⟨woodinPrefixPosetName P R one κ δ, woodinCollapseName_isName _ _ _ _⟩
  let ν : ForcingName P := ⟨rankOrderName P R δ Q.val, rankOrderName_isName _ _ _ _⟩
  have hν : ν.val ∈ hierarchy θ := subset_mem_hierarchy_limit hθ.rankCriterion.2.2.1
    (hierarchy_mem hδθ) (rankFormulaName_subset hδ.rankCriterion.2.2.1 hP _ _)
  apply formulaUniqueName_mem_hierarchy_of_semantics hR htop hθ.rankCriterion.2.2.1
    (hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hδθ) P hP)
    piOneReverseInclusionOrderFormula ![Q] ν hν
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  apply (Defined.eval_iff _).mpr
  change A.ofName ν = reverseInclusionOrder (A.ofName Q)
  apply A.rankOrder_value hδ hP Q
  let : IsOrdinal (A.ofName cδ) := by change IsOrdinal (A.check δ); infer_instance
  have he : A.ofName Q = woodinCollapse (A.check κ) (A.check δ) := A.collapseName_value_of_ordinal cκ cδ
  rw [he]
  intro p hp
  exact woodinCollapse_condition_mem_hierarchy (A.check_inaccessible_of_small hδ hP).regular
    ((A.checkEmbedding.subset_iff _ _).mpr hκ) hp

theorem forcedEmptyName_mem_hierarchy_countable {P R one θ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hθ : IsChoicelessInaccessible θ) (hP : P ∈ hierarchy θ) :
    forcedEmptyName P R ∈ hierarchy θ := by
  let := hθ.1
  let ν : ForcingName P := ⟨∅, empty_forcingName P⟩
  have hν : ν.val ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr (hθ.regular.2.1 ∅ (by simp))
  apply formulaUniqueName_mem_hierarchy_of_semantics hR htop hθ.rankCriterion.2.2.1 hP
    isEmpty (![] : Fin 0 → ForcingName P) ν hν
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  have he : A.ofName ν = ∅ := by
    apply mem_ext
    intro x
    rw [A.mem_ofName_iff]
    simp [ν]
  simpa using he

end ZFVP
