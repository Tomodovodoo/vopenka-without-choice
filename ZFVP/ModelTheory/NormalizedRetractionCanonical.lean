import ZFVP.ModelTheory.RetractionCanonicalNames
import ZFVP.ModelTheory.NormalizedCanonicalTwoStep
import ZFVP.ModelTheory.NormalizedBaseTwoStep
import ZFVP.ModelTheory.ForcingRetractionCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem normalizedNamePool_eq_of_forced_equality {P R one δ U W : V}
    (hR : IsForcingPreorder P R) (he : one ∈ atomicEquality P R U W) :
    normalizedNamePool P R one δ U = normalizedNamePool P R one δ W := by
  apply mem_ext
  intro τ
  simp only [normalizedNamePool, mem_sep_iff]
  exact and_congr Iff.rfl (and_congr Iff.rfl
    (and_congr Iff.rfl (atomicEquality_membership_iff hR he τ).2))

theorem normalizedNameTwoStep_eq_of_forced_equality {P R one δ U W : V}
    (hR : IsForcingPreorder P R) (he : one ∈ atomicEquality P R U W) :
    normalizedNameTwoStep P R one δ U = normalizedNameTwoStep P R one δ W := by
  unfold normalizedNameTwoStep
  rw [normalizedNamePool_eq_of_forced_equality hR he]

variable {P R N T m one κ δ : V}
local notation "U" => saturatedWoodinPrefixPosetName P R one κ δ
local notation "W" => saturatedWoodinPrefixPosetName N T one κ δ
local notation "S" => saturatedWoodinPrefixOrderName P R one κ δ
local notation "S'" => saturatedWoodinPrefixOrderName N T one κ δ

theorem IsForcingRetraction.normalized_prefix_carrier
    (hr : IsForcingRetraction N T P R m)
    (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ q ∈ P, ⟨m ‘ q, q⟩ₖ ∈ R ∧ ⟨q, m ‘ q⟩ₖ ∈ R)
    (ht : IsForcingTop P R one) (ho : one ∈ N)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκ : κ ⊆ δ) :
    normalizedNameTwoStep N T one δ (nameAction m U) = normalizedNameTwoStep N T one δ W := by
  apply normalizedNameTwoStep_eq_of_forced_equality hT
  have hh := hr.saturated_prefix_equality hR hT he ht ho hδ hP hκ ht.1
  rwa [hr.fixes one ho] at hh

theorem IsForcingRetraction.normalized_prefix_order
    (hr : IsForcingRetraction N T P R m)
    (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ q ∈ P, ⟨m ‘ q, q⟩ₖ ∈ R ∧ ⟨q, m ‘ q⟩ₖ ∈ R)
    (ht : IsForcingTop P R one) (ho : one ∈ N)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκ : κ ⊆ δ) :
    nameTwoStepOrderOn N T (nameAction m S) (normalizedNameTwoStep N T one δ (nameAction m U)) =
      nameTwoStepOrderOn N T S' (normalizedNameTwoStep N T one δ W) := by
  rw [hr.normalized_prefix_carrier hR hT he ht ho hδ hP hκ]
  apply nameTwoStepOrderOn_eq_of_forced_equality hT
  · intro z hz
    obtain ⟨p, hp, τ, _, rfl⟩ := mem_prod_iff.mp hz
    simpa only [kpair.π₁_kpair] using hp
  · intro q hq
    have hp := hr.inclusion q hq
    have hUW := hr.saturated_prefix_equality hR hT he ht ho hδ hP hκ hp
    have hh := hr.reverse_order_equality hR hT he ht ho hp
      ⟨U, saturatedWoodinPrefixPosetName_isName P R one κ δ⟩
      ⟨W, saturatedWoodinPrefixPosetName_isName N T one κ δ⟩ hUW
    simpa only [hr.fixes q hq, saturatedWoodinPrefixOrderName] using hh

theorem saturatedWoodinPrefix_normalizedBase_canonical_retraction
    (hr : IsForcingRetraction N T P R m)
    (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (ht : IsForcingTop P R one) (ho : one ∈ N)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκδ : κ ⊆ δ)
    (he : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R ∧ ⟨p, m ‘ p⟩ₖ ∈ R)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ])) :
    IsForcingRetraction (normalizedNameTwoStep N T one δ W)
      (nameTwoStepOrderOn N T S' (normalizedNameTwoStep N T one δ W))
      (twoStepConditions P R U ∅) (twoStepOrder P R U S ∅)
      (normalizedBaseTwoStepMap P R N T one δ U m) := by
  have hh := saturatedWoodinPrefix_normalizedBase_retraction hr hR hT ht ho hδ hP hκδ he hκ
  dsimp only at hh
  rw [hr.normalized_prefix_order hR hT he ht ho hδ hP hκδ,
    hr.normalized_prefix_carrier hR hT he ht ho hδ hP hκδ] at hh
  exact hh

end ZFVP
