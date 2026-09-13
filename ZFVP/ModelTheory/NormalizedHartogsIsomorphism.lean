import ZFVP.ModelTheory.NormalizedCanonicalTwoStep
import ZFVP.ModelTheory.SaturatedHartogsStage

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem normalizedSaturatedHartogs_isomorphism {P R A B one top δ f : V}
    (hf : IsForcingIsomorphism P R A B f)
    (hR : IsForcingPreorder P R) (hB : IsForcingPreorder A B)
    (ho : IsForcingTop P R one) (ht : IsForcingTop A B top) (hft : f ‘ one = top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hA : A ∈ hierarchy δ) (γ : V) :
    let U := saturatedHartogsPosetName P R one γ δ
    let W := saturatedHartogsPosetName A B top γ δ
    IsForcingIsomorphism (normalizedNameTwoStep P R one δ U)
      (nameTwoStepOrderOn P R (saturatedHartogsOrderName P R one γ δ) (normalizedNameTwoStep P R one δ U))
      (normalizedNameTwoStep A B top δ W)
      (nameTwoStepOrderOn A B (saturatedHartogsOrderName A B top γ δ) (normalizedNameTwoStep A B top δ W))
      (normalizedTwoStepIsoMap P R one δ U A B top f) := by
  let := hδ.1
  dsimp only
  have he : nameAction f (saturatedHartogsPosetName P R one γ δ) = saturatedHartogsPosetName A B top γ δ :=
    hf.saturated_hartogs_collapse hR hB ho ht hft γ δ
  have hi := normalizedTwoStep_reverse_order_isomorphism hf hR hB ho ht hft hδ hP hA
    (saturatedHartogsPosetName_isName P R one γ δ)
  rw [he] at hi
  exact hi

theorem normalizedHartogsSuccessor_isomorphism {P R A B one top f γ : V}
    (hf : IsForcingIsomorphism P R A B f)
    (hR : IsForcingPreorder P R) (hB : IsForcingPreorder A B)
    (ho : IsForcingTop P R one) (ht : IsForcingTop A B top) (hft : f ‘ one = top)
    (hδ : IsChoicelessInaccessible
      (woodinNamedPrefixCutoff P R one γ (hartogsNumberName P R (checkName one γ))))
    (hP : P ∈ hierarchy (woodinNamedPrefixCutoff P R one γ (hartogsNumberName P R (checkName one γ))))
    (hA : A ∈ hierarchy (woodinNamedPrefixCutoff P R one γ (hartogsNumberName P R (checkName one γ)))) :
    let δ := woodinNamedPrefixCutoff P R one γ (hartogsNumberName P R (checkName one γ))
    let ε := woodinNamedPrefixCutoff A B top γ (hartogsNumberName A B (checkName top γ))
    let U := saturatedHartogsPosetName P R one γ δ
    let W := saturatedHartogsPosetName A B top γ ε
    IsForcingIsomorphism (normalizedNameTwoStep P R one δ U)
      (nameTwoStepOrderOn P R (saturatedHartogsOrderName P R one γ δ) (normalizedNameTwoStep P R one δ U))
      (normalizedNameTwoStep A B top ε W)
      (nameTwoStepOrderOn A B (saturatedHartogsOrderName A B top γ ε) (normalizedNameTwoStep A B top ε W))
      (normalizedTwoStepIsoMap P R one δ U A B top f) := by
  dsimp only
  rw [← hf.hartogs_prefix_cutoff hR hB ho ht hft γ]
  exact normalizedSaturatedHartogs_isomorphism hf hR hB ho ht hft hδ hP hA γ

end ZFVP
