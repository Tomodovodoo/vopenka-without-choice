import ZFVP.ModelTheory.NormalizedReverseOrderComparison
import ZFVP.ModelTheory.SaturatedWoodinPrefix
import ZFVP.ModelTheory.SaturatedHartogsFormulas

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem normalizedPrefixTwoStep_order_comparison {P R one κ δ p q τ σ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hp : p ∈ P) (hq : q ∈ P)
    (hτ : τ ∈ normalizedNamePool P R one δ (saturatedWoodinPrefixPosetName P R one κ δ))
    (hσ : σ ∈ normalizedNamePool P R one δ (saturatedWoodinPrefixPosetName P R one κ δ)) :
    ⟨⟨p, τ⟩ₖ, ⟨q, σ⟩ₖ⟩ₖ ∈ nameTwoStepOrderOn P R (saturatedWoodinPrefixOrderName P R one κ δ)
      (normalizedNameTwoStep P R one δ (saturatedWoodinPrefixPosetName P R one κ δ)) ↔
      ⟨p, q⟩ₖ ∈ R ∧ p ∈ forcingFormula P R isSubsetOf (standardTuple ![σ, τ]) :=
  normalizedNameTwoStep_reverse_order_comparison hR ht
    (saturatedWoodinPrefixPosetName_isName P R one κ δ) hp hq hτ hσ

theorem normalizedHartogsTwoStep_order_comparison {P R one γ δ p q τ σ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hp : p ∈ P) (hq : q ∈ P)
    (hτ : τ ∈ normalizedNamePool P R one δ (saturatedHartogsPosetName P R one γ δ))
    (hσ : σ ∈ normalizedNamePool P R one δ (saturatedHartogsPosetName P R one γ δ)) :
    ⟨⟨p, τ⟩ₖ, ⟨q, σ⟩ₖ⟩ₖ ∈ nameTwoStepOrderOn P R (saturatedHartogsOrderName P R one γ δ)
      (normalizedNameTwoStep P R one δ (saturatedHartogsPosetName P R one γ δ)) ↔
      ⟨p, q⟩ₖ ∈ R ∧ p ∈ forcingFormula P R isSubsetOf (standardTuple ![σ, τ]) :=
  normalizedNameTwoStep_reverse_order_comparison hR ht
    (forcingSaturatedName_isName _ _ _ _) hp hq hτ hσ

end ZFVP
