import ZFVP.ModelTheory.PrefixCollapseRankDCThreshold
import ZFVP.ModelTheory.TwoStepRankDCForcingAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eventually_prefixCollapse_rankDCBelow_forcing_eq_countable [Countable V]
    {δ κ γ P R one : V} (hδ : IsWoodinSupercompact δ) (hP : P ∈ hierarchy δ)
    (hκδ : κ ∈ δ) (hγδ : γ ∈ δ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![checkName one κ])) :
    ∃ β ∈ δ, γ ∈ β ∧ ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
      let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
      let q := woodinCollapse (A.check κ) (A.check γ)
      let s := woodinCollapseOrder (A.check κ) (A.check γ)
      ∀ ξ : A.Model, A.check β ∈ ξ → IsChoicelessInaccessible ξ → q ∈ hierarchy ξ →
        checkName ∅ (A.check γ) ∈ hierarchy ξ →
        classForcingFormula q s (IsLowRankForcingName q ξ) (by definability)
          dependentChoiceBelowFormula (standardTuple ![checkName ∅ (A.check γ)]) =
        forcingFormula q s dependentChoiceBelowFormula
          (standardTuple ![checkName ∅ (A.check γ)]) := by
  let := hδ.1.1
  let := IsOrdinal.of_mem hκδ
  let := IsOrdinal.of_mem hγδ
  obtain ⟨θ, hθδ, hθ, hPθ, hκθ, hγθ⟩ := hδ.prefixCollapse_name_height hP hκδ hγδ
  let := hθ.ordinal
  have h0 : (∅ : V) ∈ θ := IsOrdinal.toIsTransitive.mem_trans (show (∅ : V) ∈ ω by simp) hθ.omega_lt
  let h := boundedPrefixCollapse_iterand (κ := κ) (γ := γ) hR ht h0 hκ
  obtain ⟨β, hβ, hγβ, hall⟩ := eventually_twoStep_rankDCBelow_forcing_eq_countable hδ
    (boundedPrefixCollapse_twoStep_small hδ.inaccessible hP hθδ) hγδ hR ht h
  refine ⟨β, hβ, hγβ, ?_⟩
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  have hp := A.boundedPrefixCollapseName_value hθ hPθ hκθ hγθ
  have hs : A.ofName ⟨reverseInclusionOrderName P R (boundedPrefixCollapseName P R one κ γ θ),
      h.orderName⟩ = woodinCollapseOrder (A.check κ) (A.check γ) := by
    change A.ofName (A.reverseOrderName ⟨boundedPrefixCollapseName P R one κ γ θ, h.posetName⟩) = _
    rw [A.reverseOrderName_value, hp]
    rfl
  have ho : A.ofName ⟨∅, h.topName⟩ = ∅ := by
    apply mem_ext
    intro x
    rw [A.mem_ofName_iff]
    simp
  have hh := hall G hG
  change ∀ ξ : A.Model, A.check β ∈ ξ → IsChoicelessInaccessible ξ →
    A.ofName ⟨boundedPrefixCollapseName P R one κ γ θ, h.posetName⟩ ∈ hierarchy ξ →
    checkName (A.ofName ⟨∅, h.topName⟩) (A.check γ) ∈ hierarchy ξ →
    classForcingFormula _ _ (IsLowRankForcingName _ ξ) (by definability)
      dependentChoiceBelowFormula (standardTuple ![checkName (A.ofName ⟨∅, h.topName⟩) (A.check γ)]) =
    forcingFormula _ _ dependentChoiceBelowFormula
      (standardTuple ![checkName (A.ofName ⟨∅, h.topName⟩) (A.check γ)]) at hh
  dsimp only [A] at hp hs ho hh
  simpa only [hp, hs, ho] using hh

end ZFVP
