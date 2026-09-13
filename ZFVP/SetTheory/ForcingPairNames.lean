import ZFVP.SetTheory.ForcingNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def pairName (p σ τ : V) : V := {⟨σ, p⟩ₖ, ⟨τ, p⟩ₖ}

instance pairName_definable : ℒₛₑₜ-function₃[V] pairName := by
  unfold pairName
  definability

theorem pairName_isName {P p σ τ : V} (hp : p ∈ P) (hσ : IsForcingName P σ) (hτ : IsForcingName P τ) :
    IsForcingName P (pairName p σ τ) := forcingName_pair hσ hτ hp

noncomputable def orderedPairName (p σ τ : V) : V := pairName p (pairName p σ σ) (pairName p σ τ)

instance orderedPairName_definable : ℒₛₑₜ-function₃[V] orderedPairName := by
  unfold orderedPairName
  definability

theorem orderedPairName_isName {P p σ τ : V} (hp : p ∈ P) (hσ : IsForcingName P σ)
    (hτ : IsForcingName P τ) : IsForcingName P (orderedPairName p σ τ) :=
  pairName_isName hp (pairName_isName hp hσ hσ) (pairName_isName hp hσ hτ)

end ZFVP
