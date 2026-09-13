import ZFVP.ModelTheory.NormalizedTwoStepIsomorphism
import ZFVP.ModelTheory.ForcingIsomorphismWoodinSuccessor

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameTwoStepOrderOn_eq_of_forced_equality {P R S T C : V}
    (hR : IsForcingPreorder P R) (hC : ∀ z ∈ C, kpair.π₁ z ∈ P)
    (he : ∀ p ∈ P, p ∈ atomicEquality P R S T) :
    nameTwoStepOrderOn P R S C = nameTwoStepOrderOn P R T C := by
  apply mem_ext
  intro z
  simp only [nameTwoStepOrderOn, mem_sep_iff]
  apply and_congr_right
  intro hz
  obtain ⟨a, ha, b, _, rfl⟩ := mem_prod_iff.mp hz
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  apply and_congr Iff.rfl
  have hp := hC a ha
  apply classForcingFormula_congr hR (IsForcingName P) (by definability)
    boundedPairMemberFormula _ _ hp
  intro i
  exact Fin.cases (he _ hp) (fun j ↦ Fin.cases
    ((atomicEquality_refl hR (kpair.π₂ a)).symm ▸ hp)
    (fun k ↦ Fin.cases ((atomicEquality_refl hR (kpair.π₂ b)).symm ▸ hp)
      (fun l ↦ Fin.elim0 l) k) j) i

theorem normalizedTwoStep_reverse_order_isomorphism {P R A B one top δ U f : V}
    (hf : IsForcingIsomorphism P R A B f)
    (hR : IsForcingPreorder P R) (hB : IsForcingPreorder A B)
    (ho : IsForcingTop P R one) (ht : IsForcingTop A B top) (hft : f ‘ one = top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hA : A ∈ hierarchy δ)
    (hU : IsForcingName P U) :
    IsForcingIsomorphism (normalizedNameTwoStep P R one δ U)
      (nameTwoStepOrderOn P R (reverseInclusionOrderName P R U) (normalizedNameTwoStep P R one δ U))
      (normalizedNameTwoStep A B top δ (nameAction f U))
      (nameTwoStepOrderOn A B (reverseInclusionOrderName A B (nameAction f U))
        (normalizedNameTwoStep A B top δ (nameAction f U)))
      (normalizedTwoStepIsoMap P R one δ U A B top f) := by
  have hi := normalizedTwoStepIsoMap_isomorphism hf hR hB ho.1 ht hft hδ hP hA hU
    (reverseInclusionOrderName_isName P R U)
  have he : nameTwoStepOrderOn A B (nameAction f (reverseInclusionOrderName P R U))
      (normalizedNameTwoStep A B top δ (nameAction f U)) =
      nameTwoStepOrderOn A B (reverseInclusionOrderName A B (nameAction f U))
        (normalizedNameTwoStep A B top δ (nameAction f U)) := by
    apply nameTwoStepOrderOn_eq_of_forced_equality hB
    · intro z hz
      obtain ⟨p, hp, τ, _, rfl⟩ := mem_prod_iff.mp hz
      simpa only [kpair.π₁_kpair] using hp
    · intro q hq
      have hp := function_value_mem hf.inverse_maps hq
      have hh := hf.reverse_order_name_equality hR hB ho ht hp
        ⟨U, hU⟩ ⟨nameAction f U, nameAction_isName hf.1 hU⟩
        ((atomicEquality_refl hB (nameAction f U)).symm ▸ function_value_mem hf.1 hp)
      simpa only [hf.value_inverse hq] using hh
  rw [he] at hi
  exact hi

theorem normalizedSaturatedPrefix_isomorphism {P R A B one top δ f : V}
    (hf : IsForcingIsomorphism P R A B f)
    (hR : IsForcingPreorder P R) (hB : IsForcingPreorder A B)
    (ho : IsForcingTop P R one) (ht : IsForcingTop A B top) (hft : f ‘ one = top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hA : A ∈ hierarchy δ)
    (κ : V) :
    let U := saturatedWoodinPrefixPosetName P R one κ δ
    let W := saturatedWoodinPrefixPosetName A B top κ δ
    IsForcingIsomorphism (normalizedNameTwoStep P R one δ U)
      (nameTwoStepOrderOn P R (saturatedWoodinPrefixOrderName P R one κ δ)
        (normalizedNameTwoStep P R one δ U))
      (normalizedNameTwoStep A B top δ W)
      (nameTwoStepOrderOn A B (saturatedWoodinPrefixOrderName A B top κ δ)
        (normalizedNameTwoStep A B top δ W))
      (normalizedTwoStepIsoMap P R one δ U A B top f) := by
  let := hδ.1
  dsimp only
  have hi := normalizedTwoStep_reverse_order_isomorphism hf hR hB ho ht hft hδ hP hA
    (saturatedWoodinPrefixPosetName_isName P R one κ δ)
  rw [hf.saturated_prefix_name hR hB ho ht hft κ] at hi
  exact hi

theorem normalizedPrefixSuccessor_isomorphism {P R A B one top f κ : V}
    (hf : IsForcingIsomorphism P R A B f)
    (hR : IsForcingPreorder P R) (hB : IsForcingPreorder A B)
    (ho : IsForcingTop P R one) (ht : IsForcingTop A B top) (hft : f ‘ one = top)
    (hδ : IsChoicelessInaccessible (woodinPrefixCutoff P R one κ))
    (hP : P ∈ hierarchy (woodinPrefixCutoff P R one κ))
    (hA : A ∈ hierarchy (woodinPrefixCutoff P R one κ)) :
    let δ := woodinPrefixCutoff P R one κ
    let ε := woodinPrefixCutoff A B top κ
    let U := saturatedWoodinPrefixPosetName P R one κ δ
    let W := saturatedWoodinPrefixPosetName A B top κ ε
    IsForcingIsomorphism (normalizedNameTwoStep P R one δ U)
      (nameTwoStepOrderOn P R (saturatedWoodinPrefixOrderName P R one κ δ)
        (normalizedNameTwoStep P R one δ U))
      (normalizedNameTwoStep A B top ε W)
      (nameTwoStepOrderOn A B (saturatedWoodinPrefixOrderName A B top κ ε)
        (normalizedNameTwoStep A B top ε W))
      (normalizedTwoStepIsoMap P R one δ U A B top f) := by
  dsimp only
  rw [← hf.prefix_cutoff hR hB ho ht hft κ]
  exact normalizedSaturatedPrefix_isomorphism hf hR hB ho ht hft hδ hP hA κ

end ZFVP
