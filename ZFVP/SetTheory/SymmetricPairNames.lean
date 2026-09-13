import ZFVP.SetTheory.ForcingPairNames
import ZFVP.SetTheory.HereditarySymmetry
import ZFVP.SetTheory.NameValue

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameAction_orderedPairName {P p σ τ : V} (hp : p ∈ P)
    (hσ : IsForcingName P σ) (hτ : IsForcingName P τ) (π : V) :
    nameAction π (orderedPairName p σ τ) =
      orderedPairName (π ‘ p) (nameAction π σ) (nameAction π τ) := by
  unfold orderedPairName pairName
  rw [nameAction_pair (forcingName_pair hσ hσ hp) (forcingName_pair hσ hτ hp) hp,
    nameAction_pair hσ hσ hp, nameAction_pair hσ hτ hp]

theorem hereditarilySymmetric_orderedPairName {P R Γ F one σ τ : V}
    (hR : IsForcingPoset P R) (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hF : IsNormalSubgroupFilter P Γ F) (hone : IsForcingTop P R one)
    (hσ : IsHereditarilySymmetricName P Γ F σ) (hτ : IsHereditarilySymmetricName P Γ F τ) :
    IsHereditarilySymmetricName P Γ F (orderedPairName one σ τ) :=
  hereditarilySymmetric_pair hR hΓ hF hone
    (hereditarilySymmetric_pair hR hΓ hF hone hσ hσ)
    (hereditarilySymmetric_pair hR hΓ hF hone hσ hτ)

theorem nameValue_orderedPairName {G p : V} (hp : p ∈ G) (σ τ : V) :
    nameValue G (orderedPairName p σ τ) = ⟨nameValue G σ, nameValue G τ⟩ₖ := by
  unfold orderedPairName pairName
  rw [nameValue_pair hp, nameValue_pair hp, nameValue_pair hp]
  simp [kpair]

end ZFVP

