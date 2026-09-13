import ZFVP.ModelTheory.SigmaThreeInverseCardinalNext
import ZFVP.ModelTheory.WoodinInverseSourceCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

theorem woodinInverseStage_deltaThree_on_iteration :
    ∃ σ π σc πc : SetTheorySemisentence 4,
      IsSigmaFormula 3 σ ∧ IsPiFormula 3 π ∧ IsSigmaFormula 3 σc ∧ IsPiFormula 3 πc ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙], ∀ δ θ s K : V,
        IsOrdinal θ → IsWoodinIteration δ θ s K → IsWoodinSupercompact δ → θ ∈ δ → ∅ ∈ θ →
        (∀ p ∈ forcingInverseCodePoset θ s,
          p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
            (regularCardinalFormula.or limitOfRegularCardinalsFormula)
            (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)])) →
        (∀ p ∈ forcingInverseCodePoset θ s,
          p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
            dependentChoiceAtFormula
            (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)])) → ∀ z,
          (σ.Evalb ![z, θ, s, K] ↔ z = woodinInverseSourceCode θ s K) ∧
          (π.Evalb ![z, θ, s, K] ↔ z = woodinInverseSourceCode θ s K) ∧
          (σc.Evalb ![z, θ, s, K] ↔ z = woodinInverseCardinalNext θ s K) ∧
          (πc.Evalb ![z, θ, s, K] ↔ z = woodinInverseCardinalNext θ s K) := by
  obtain ⟨σ, π, hσ, hπ, hcode⟩ := woodinInverseSourceCode_deltaThree_uniform.{u}
  obtain ⟨σc, πc, hσc, hπc, hcard⟩ := woodinInverseCardinalNext_deltaThree_uniform.{u}
  refine ⟨σ, π, σc, πc, hσ, hπ, hσc, hπc, ?_⟩
  intro V _ _ _ δ θ s K hθ h hδ hθδ h0 hγ hDC z
  let := hθ
  have c := h.code.system.inverseColumn h0 h.code.subset_universe
  have ht : IsForcingTop (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodeTop θ s) := c.tops.top
  have hreg : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        regularCardinalFormula (standardTuple ![forcingInverseHartogsName θ s (woodinLimitCardinal K)]) := by
    intro p hp
    exact hartogsNumberName_forces_regular c.order.preorder ht hp
      ⟨checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K), checkName_isName ht.1 _⟩
      (hγ p hp) (hDC p hp)
  have hc := (h.inverse_sourceCutoff hδ hθδ h0 hγ hDC).2
  have hC := hcode V θ s K c.order.preorder ht hreg ⟨_, hc⟩ z
  have hK := hcard V θ s K c.order.preorder ht hreg ⟨_, hc⟩ z
  exact ⟨hC.1, hC.2, hK.1, hK.2⟩

end ZFVP
