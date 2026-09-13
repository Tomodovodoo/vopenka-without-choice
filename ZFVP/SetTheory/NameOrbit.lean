import ZFVP.SetTheory.SymmetryAction

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def nameOrbit (H B : V) : V :=
  repl (fun z ↦ nameAction (kpair.π₁ z) (kpair.π₂ z)) (by definability) (H ×ˢ B)

theorem mem_nameOrbit_iff (H B ν : V) :
    ν ∈ nameOrbit H B ↔ ∃ π ∈ H, ∃ τ ∈ B, ν = nameAction π τ := by
  simp only [nameOrbit, repl_spec, mem_prod_iff]
  constructor
  · rintro ⟨z, ⟨π, hπ, τ, hτ, rfl⟩, he⟩
    exact ⟨π, hπ, τ, hτ, by simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using he⟩
  · rintro ⟨π, hπ, τ, hτ, rfl⟩
    exact ⟨⟨π, τ⟩ₖ, ⟨π, hπ, τ, hτ, rfl⟩, by simp only [kpair.π₁_kpair, kpair.π₂_kpair]⟩

theorem subset_nameOrbit {P Γ H B : V} (hH : IsForcingSubgroup P Γ H)
    (hB : ∀ τ ∈ B, IsForcingName P τ) : B ⊆ nameOrbit H B := by
  intro τ hτ
  exact (mem_nameOrbit_iff _ _ _).mpr ⟨identity P, hH.2.1, τ, hτ, (nameAction_identity (hB τ hτ)).symm⟩

theorem hereditarilySymmetric_mem_nameOrbit {P R Γ F H B : V}
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hF : IsNormalSubgroupFilter P Γ F)
    (hH : IsForcingSubgroup P Γ H) (hB : ∀ τ ∈ B, IsHereditarilySymmetricName P Γ F τ)
    {ν : V} (hν : ν ∈ nameOrbit H B) : IsHereditarilySymmetricName P Γ F ν := by
  obtain ⟨π, hπ, τ, hτ, rfl⟩ := (mem_nameOrbit_iff _ _ _).mp hν
  exact hereditarilySymmetric_nameAction hΓ hF (hH.1 π hπ) (hB τ hτ)

theorem nameOrbit_action_closed {P R Γ H B π ν : V}
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hH : IsForcingSubgroup P Γ H)
    (hB : ∀ τ ∈ B, IsForcingName P τ) (hπ : π ∈ H) (hν : ν ∈ nameOrbit H B) :
    nameAction π ν ∈ nameOrbit H B := by
  obtain ⟨ρ, hρ, τ, hτ, rfl⟩ := (mem_nameOrbit_iff _ _ _).mp hν
  exact (mem_nameOrbit_iff _ _ _).mpr ⟨compose ρ π, hH.2.2.1 ρ hρ π hπ, τ, hτ,
    nameAction_compose (hΓ.1 ρ (hH.1 ρ hρ)).1 (hΓ.1 π (hH.1 π hπ)).1 (hB τ hτ)⟩

theorem nameOrbit_action_iff {P R Γ H B π ν : V}
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hH : IsForcingSubgroup P Γ H)
    (hB : ∀ τ ∈ B, IsForcingName P τ) (hπ : π ∈ H) (hν : IsForcingName P ν) :
    nameAction π ν ∈ nameOrbit H B ↔ ν ∈ nameOrbit H B := by
  constructor
  · intro hh
    have hi := nameOrbit_action_closed hΓ hH hB (hH.2.2.2 π hπ) hh
    simpa only [nameAction_inverse_cancel (hΓ.1 π (hH.1 π hπ)) hν] using hi
  · exact nameOrbit_action_closed hΓ hH hB hπ

end ZFVP
