import ZFVP.ModelTheory.TwoStepRankDCThreshold
import ZFVP.ModelTheory.ForcingRankDCBelowAgreement
import ZFVP.ModelTheory.ForcingRegularGenericEquality

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eventually_twoStep_rankDCBelow_forcing_eq_countable [Countable V]
    {δ γ P R Q S t one : V} (hδ : IsWoodinSupercompact δ)
    (hC : twoStepConditions P R Q t ∈ hierarchy δ) (hγ : γ ∈ δ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (h : IsForcingIterand P R Q S t) :
    ∃ β ∈ δ, γ ∈ β ∧ ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
      let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
      let q := A.ofName ⟨Q, h.posetName⟩
      let s := A.ofName ⟨S, h.orderName⟩
      let o := A.ofName ⟨t, h.topName⟩
      ∀ ξ : A.Model, A.check β ∈ ξ → IsChoicelessInaccessible ξ → q ∈ hierarchy ξ →
        checkName o (A.check γ) ∈ hierarchy ξ →
        classForcingFormula q s (IsLowRankForcingName q ξ) (by definability)
          dependentChoiceBelowFormula (standardTuple ![checkName o (A.check γ)]) =
        forcingFormula q s dependentChoiceBelowFormula
          (standardTuple ![checkName o (A.check γ)]) := by
  obtain ⟨β, hβ, hγβ, hall⟩ := uniform_twoStep_rankDCThreshold hδ hC hγ hR ht h
  refine ⟨β, hβ, hγβ, ?_⟩
  intro G hG
  dsimp only
  intro ξ hβξ hξ hQ hn
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  apply IsForcingRegular.eq_of_all_generics (TwoStepModel.preorder A h)
    (classForcingFormula_regular _ _ (TwoStepModel.preorder A h) _ _)
    (forcingFormula_regular (TwoStepModel.preorder A h) _ _)
  intro H hH
  let B := TwoStepModel.iterandContext A h hH
  exact B.rankDCBelow_classForcing_iff hξ hQ hn (hall G hG H hH)
    ((B.check_mem_iff _ _).mpr hβξ)

end ZFVP
