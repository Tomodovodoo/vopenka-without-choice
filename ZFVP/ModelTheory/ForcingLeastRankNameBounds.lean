import ZFVP.ModelTheory.ForcingLeastRankNormalization
import ZFVP.ModelTheory.CanonicalNormalizationForcing
import ZFVP.SetTheory.ForcingNameHierarchyBound

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsChoicelessInaccessible.forcingNameHierarchy_subset {δ P : V}
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) :
    forcingNameHierarchy P δ ⊆ hierarchy δ := by
  let := hδ.1
  intro τ hτ
  obtain ⟨β, hβδ, hτβ⟩ := (mem_forcingNameHierarchy _ _ _).mp hτ
  exact subset_mem_hierarchy_limit hδ.rankCriterion.2.2.1
    (prod_mem_hierarchy_limit hδ.rankCriterion.2.2.1
      (forcingNameHierarchy_mem_hierarchy hδ hP hβδ) hP) hτβ

/-- A forced value-rank bound gives a ground-rank bound on the exact least-rank
union normalization. The input name need not belong to the rank. -/
theorem forcingLeastRankName_mem_of_forced_rank {P R one δ p τ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hp : p ∈ P) (hτ : IsForcingName P τ)
    (hf : p ∈ forcingFormula P R nameInHierarchyFormula (standardTuple ![τ, checkName one δ])) :
    forcingLeastRankName P R p τ ∈ hierarchy δ := by
  let := hδ.1
  have hn := forcingCanonicalName_mem hR ht hδ hP τ
  have he := forcingCanonicalName_forces hR ht hδ hP hp ⟨τ, hτ⟩ hf
  apply forcingLeastRankName_mem_hierarchy_of_equiv hR hp hτ
    (forcingCanonicalName_isName P R one δ τ)
  · rwa [atomicEquality_symm]
  · exact hδ.forcingNameHierarchy_subset hP _ hn

namespace ForcingContext

theorem leastRankName_value (A : ForcingContext V) {p : V} (hp : p ∈ A.G)
    (τ : ForcingName A.P) :
    A.ofName ⟨forcingLeastRankName A.P A.R p τ.val,
      forcingLeastRankName_isName A.order (A.generic.1.1 p hp) τ.property⟩ = A.ofName τ := by
  apply (forcingQuotientMk_eq_iff A.P A.R A.G A.order A.generic.1 _ _).mpr
  refine ⟨p, hp, ?_⟩
  rw [atomicEquality_symm]
  exact forcingLeastRankName_forced_equal A.order (A.generic.1.1 p hp) τ.property

end ForcingContext
end ZFVP
