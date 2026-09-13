import ZFVP.SetTheory.CohenRepresentativeSupport
import ZFVP.SetTheory.Collection

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Strong collection bounds supported representatives for every name in `A` and every Cohen
condition. It does not choose one representative for each input. -/
theorem cohen_representative_pool {A : V}
    (hA : ∀ τ ∈ A, IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) τ) :
    ∃ D : V, (∀ z ∈ D, ∃ ν E, z = ⟨ν, E⟩ₖ ∧
        IsHereditarilySymmetricName (cohenConditions (ω : V))
          (cohenGroup (ω : V)) (cohenFilter (ω : V)) ν ∧ IsCohenNameSupport ν E) ∧
      ∀ τ ∈ A, ∀ p ∈ cohenConditions (ω : V), ∃ ν,
        ⟨ν, cohenRepresentativeLeastSupport τ p⟩ₖ ∈ D ∧
        p ∈ atomicEquality (cohenConditions (ω : V)) (cohenOrder (ω : V)) ν τ := by
  let Q := fun x y : V ↦ ∃ ν,
    y = ⟨ν, cohenRepresentativeLeastSupport (kpair.π₁ x) (kpair.π₂ x)⟩ₖ ∧
    IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) ν ∧
    kpair.π₂ x ∈ atomicEquality (cohenConditions (ω : V)) (cohenOrder (ω : V)) ν (kpair.π₁ x) ∧
    IsCohenNameSupport ν (cohenRepresentativeLeastSupport (kpair.π₁ x) (kpair.π₂ x))
  have hQ : ℒₛₑₜ-relation Q := by
    dsimp [Q]
    definability
  have hex : ∀ x ∈ A ×ˢ cohenConditions (ω : V), ∃ y, Q x y := by
    intro x hx
    obtain ⟨τ, hτ, p, hp, rfl⟩ := mem_prod_iff.mp hx
    obtain ⟨ν, hν, he, hs⟩ := cohenRepresentativeLeastSupport_isSupport (hA τ hτ) hp
    refine ⟨⟨ν, cohenRepresentativeLeastSupport τ p⟩ₖ, ν, ?_⟩
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact ⟨True.intro, hν, he, hs⟩
  obtain ⟨D, hcover, hvalid⟩ := strongCollection (A ×ˢ cohenConditions (ω : V)) Q hQ hex
  refine ⟨D, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, _, ν, he, hν, _, hs⟩ := hvalid z hz
    exact ⟨ν, cohenRepresentativeLeastSupport (kpair.π₁ x) (kpair.π₂ x), he, hν, hs⟩
  · intro τ hτ p hp
    obtain ⟨z, hz, ν, he, _, hforce, _⟩ :=
      hcover ⟨τ, p⟩ₖ (kpair_mem_iff.mpr ⟨hτ, hp⟩)
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at he hforce
    exact ⟨ν, he ▸ hz, hforce⟩

end ZFVP



