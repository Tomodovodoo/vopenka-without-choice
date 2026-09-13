import ZFVP.SetTheory.RankDCThreshold
import ZFVP.ModelTheory.WoodinCollapseForcesRestoration
import ZFVP.ModelTheory.TransitiveZFBoundedQuantifiers

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsRankDCThreshold.dependentChoiceBelow_iff {γ η ξ : V}
    (ht : IsRankDCThreshold γ η) (hηξ : η ∈ ξ) (hξ : IsChoicelessInaccessible ξ)
    (hγ : γ ∈ hierarchy ξ) :
    letI := hξ.1
    letI := rankDomain_nonempty hξ.2.1
    letI := hξ.rankCriterion.models_zf
    dependentChoiceBelowFormula.Evalb (show Fin 1 → SetDomain (hierarchy ξ) from ![⟨γ, hγ⟩]) ↔
      dependentChoiceBelowFormula.Evalb ![γ] := by
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := hierarchy_transitive ξ
  have ha := ((rankDCThreshold_iff γ η).mp ht).2 ξ hηξ hξ
  simp only [dependentChoiceBelowFormula]
  simp
  constructor
  · intro h κ hκ
    have hkξ := (hierarchy_transitive ξ).mem_trans hκ hγ
    exact (ha ⟨κ, hkξ⟩ hκ).mp (h ⟨κ, hkξ⟩ hκ)
  · intro h κ hκ
    exact (ha κ hκ).mpr (h κ.val hκ)

end ZFVP
