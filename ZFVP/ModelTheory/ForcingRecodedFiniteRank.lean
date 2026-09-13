import ZFVP.ModelTheory.ForcingRecodedGraphBounds
import ZFVP.ModelTheory.ForcingRecodedSystem
import ZFVP.ModelTheory.ForcingIterationFiniteRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ s Q T m γ : V} [IsOrdinal γ]

theorem forcingRecodedCode_finiteRank
    (hs : IsForcingIterationCode θ s)
    (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
      (Q ‘ i) (T ‘ i) (m ‘ i))
    (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
    (hQ : IsIterationTable θ Q) (hRt : IsIterationTable θ T)
    (hθ : θ ∈ hierarchy (ordinalAdd γ (ω : V)))
    (hP : ∀ i ∈ θ, Q ‘ i ⊆ hierarchy γ) :
    forcingRecodedCode θ s Q T m ∈ hierarchy (ordinalAdd γ (ω : V)) := by
  have hc := forcingRecoded_code hs hm hT hQ hRt
  have hh := hc.finiteRank (γ := γ) hθ
  simp only [forcingRecodedCode, forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code,
    forcingCodeE_code, forcingCodeL_code, forcingCodet_code] at hh ⊢
  exact hh hP (fun i hi j hj ↦ forcingRecodedProjections_graph_bound hm hi hj)
    (fun i hi j hj ↦ forcingRecodedSections_graph_bound hm hi hj)
    (fun i hi j hj ↦ forcingRecodedLifts_graph_bound hm hi hj)

end ZFVP
