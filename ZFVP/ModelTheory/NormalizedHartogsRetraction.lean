import ZFVP.ModelTheory.RetractionHartogsNames
import ZFVP.ModelTheory.NormalizedRetractionCanonical

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {P R N T m one γ δ : V}
local notation "U" => saturatedHartogsPosetName P R one γ δ
local notation "W" => saturatedHartogsPosetName N T one γ δ
local notation "S" => saturatedHartogsOrderName P R one γ δ
local notation "S'" => saturatedHartogsOrderName N T one γ δ

theorem IsForcingRetraction.normalized_hartogs_carrier
    (hr : IsForcingRetraction N T P R m)
    (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ q ∈ P, ⟨m ‘ q, q⟩ₖ ∈ R ∧ ⟨q, m ‘ q⟩ₖ ∈ R)
    (ht : IsForcingTop P R one) (ho : one ∈ N)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hγ : γ ∈ δ) :
    normalizedNameTwoStep N T one δ (nameAction m U) = normalizedNameTwoStep N T one δ W := by
  apply normalizedNameTwoStep_eq_of_forced_equality hT
  have hh := hr.saturated_hartogs_equality hR hT he ht ho hδ hP hγ ht.1
  rwa [hr.fixes one ho] at hh

theorem IsForcingRetraction.normalized_hartogs_order
    (hr : IsForcingRetraction N T P R m)
    (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ q ∈ P, ⟨m ‘ q, q⟩ₖ ∈ R ∧ ⟨q, m ‘ q⟩ₖ ∈ R)
    (ht : IsForcingTop P R one) (ho : one ∈ N)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hγ : γ ∈ δ) :
    nameTwoStepOrderOn N T (nameAction m S) (normalizedNameTwoStep N T one δ (nameAction m U)) =
      nameTwoStepOrderOn N T S' (normalizedNameTwoStep N T one δ W) := by
  rw [hr.normalized_hartogs_carrier hR hT he ht ho hδ hP hγ]
  apply nameTwoStepOrderOn_eq_of_forced_equality hT
  · intro z hz
    obtain ⟨p, hp, τ, _, rfl⟩ := mem_prod_iff.mp hz
    simpa only [kpair.π₁_kpair] using hp
  · intro q hq
    have hp := hr.inclusion q hq
    have hUW := hr.saturated_hartogs_equality hR hT he ht ho hδ hP hγ hp
    have hh := hr.reverse_order_equality hR hT he ht ho hp
      ⟨U, saturatedHartogsPosetName_isName P R one γ δ⟩
      ⟨W, saturatedHartogsPosetName_isName N T one γ δ⟩ hUW
    simpa only [hr.fixes q hq, saturatedHartogsOrderName] using hh

end ZFVP
