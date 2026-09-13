import ZFVP.SetTheory.HereditarySymmetry

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameAction_inverse_cancel {P R π τ : V} (hπ : IsForcingAutomorphism P R π)
    (hτ : IsForcingName P τ) : nameAction (converseGraph π) (nameAction π τ) = τ := by
  rw [nameAction_compose hπ.1 (forcingAutomorphism_inverse hπ).1 hτ,
    forcingAutomorphism_compose_inverse hπ, nameAction_identity hτ]

theorem nameAction_cancel_inverse {P R π τ : V} (hπ : IsForcingAutomorphism P R π)
    (hτ : IsForcingName P τ) : nameAction π (nameAction (converseGraph π) τ) = τ := by
  rw [nameAction_compose (forcingAutomorphism_inverse hπ).1 hπ.1 hτ,
    forcingAutomorphism_inverse_compose hπ, nameAction_identity hτ]

theorem nameAction_injective {P R π σ τ : V} (hπ : IsForcingAutomorphism P R π)
    (hσ : IsForcingName P σ) (hτ : IsForcingName P τ)
    (he : nameAction π σ = nameAction π τ) : σ = τ := by
  have h := congrArg (nameAction (converseGraph π)) he
  simpa only [nameAction_inverse_cancel hπ hσ, nameAction_inverse_cancel hπ hτ] using h

theorem nameAction_conjugate {P R π ρ τ : V} (hπ : IsForcingAutomorphism P R π)
    (hρ : IsForcingAutomorphism P R ρ) (hτ : IsForcingName P τ) :
    nameAction (compose (compose (converseGraph π) ρ) π) (nameAction π τ) = nameAction π (nameAction ρ τ) := by
  have hi := forcingAutomorphism_inverse hπ
  have him := forcingAutomorphism_compose hi hρ
  rw [← nameAction_compose him.1 hπ.1 (nameAction_isName hπ.1 hτ),
    ← nameAction_compose hi.1 hρ.1 (nameAction_isName hπ.1 hτ), nameAction_inverse_cancel hπ hτ]

theorem conjugate_nameStabilizer_subset {P R Γ π τ : V} (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hπ : π ∈ Γ) (hτ : IsForcingName P τ) :
    conjugateSubgroup π (nameStabilizer Γ τ) ⊆ nameStabilizer Γ (nameAction π τ) := by
  intro θ hθ
  obtain ⟨ρ, hρ, rfl⟩ := (repl_spec (by definability)).mp hθ
  obtain ⟨hρΓ, hρτ⟩ := mem_sep_iff.mp hρ
  refine mem_sep_iff.mpr ⟨hΓ.2.2.1 _ (hΓ.2.2.1 _ (hΓ.2.2.2 π hπ) ρ hρΓ) π hπ, ?_⟩
  rw [nameAction_conjugate (hΓ.1 π hπ) (hΓ.1 ρ hρΓ) hτ, hρτ]

theorem symmetric_nameAction {P R Γ F π τ : V} (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hF : IsNormalSubgroupFilter P Γ F) (hπ : π ∈ Γ) (hτ : IsSymmetricName P Γ F τ) :
    IsSymmetricName P Γ F (nameAction π τ) := by
  have hn := nameAction_isName (hΓ.1 π hπ).1 hτ.1
  refine ⟨hn, ?_⟩
  exact hF.2.2.1 _ (hF.2.2.2.2 π hπ _ hτ.2) _ (nameStabilizer_subgroup hΓ hn)
    (conjugate_nameStabilizer_subset hΓ hπ hτ.1)

theorem hereditarilySymmetric_nameAction {P R Γ F π τ : V} (hΓ : IsForcingAutomorphismGroup P R Γ)
    (hF : IsNormalSubgroupFilter P Γ F) (hπ : π ∈ Γ) (hτ : IsHereditarilySymmetricName P Γ F τ) :
    IsHereditarilySymmetricName P Γ F (nameAction π τ) := by
  refine ⟨nameAction_isName (hΓ.1 π hπ).1 hτ.1, ?_⟩
  intro σ hσ
  rw [nameClosure_nameAction hτ.1] at hσ
  obtain ⟨υ, hυ, rfl⟩ := (repl_spec (by definability)).mp hσ
  exact (symmetric_nameAction hΓ hF hπ
    (hereditarilySymmetric_symmetric (hereditarilySymmetric_mem_closure hτ hυ))).2

end ZFVP
