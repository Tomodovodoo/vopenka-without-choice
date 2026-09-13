import ZFVP.ModelTheory.ForcingRegularGenericEquality
import ZFVP.ModelTheory.ForcingRankDCBelowAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eventually_rankDCBelow_forcing_eq_countable [Countable V] {δ γ P R one : V}
    (hδ : IsWoodinSupercompact δ) (hP : P ∈ hierarchy δ) (hγ : γ ∈ δ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) :
    ∃ β ∈ δ, γ ∈ β ∧ ∀ ξ, β ∈ ξ → IsChoicelessInaccessible ξ → P ∈ hierarchy ξ →
      checkName one γ ∈ hierarchy ξ →
      classForcingFormula P R (IsLowRankForcingName P ξ) (by definability)
        dependentChoiceBelowFormula (standardTuple ![checkName one γ]) =
      forcingFormula P R dependentChoiceBelowFormula (standardTuple ![checkName one γ]) := by
  obtain ⟨β, hβ, hγβ, hall⟩ := uniform_rankDCThreshold_all_generics hδ hP hγ hR ht
  refine ⟨β, hβ, hγβ, ?_⟩
  intro ξ hβξ hξ hPξ hn
  apply IsForcingRegular.eq_of_all_generics hR
    (classForcingFormula_regular _ _ hR _ _) (forcingFormula_regular hR _ _)
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  exact A.rankDCBelow_classForcing_iff hξ hPξ hn (hall G hG)
    ((A.check_mem_iff _ _).mpr hβξ)

end ZFVP
