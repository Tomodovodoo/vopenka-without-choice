import ZFVP.SetTheory.NameActionMembership

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameAction_bounded {P R π ρ τ : V} (hπ : IsForcingAutomorphism P R π)
    (hρ : IsForcingName P ρ) (hτ : IsForcingName P τ) (hb : ρ ⊆ domain τ ×ˢ P) :
    nameAction π ρ ⊆ domain (nameAction π τ) ×ˢ P := by
  intro z hz
  obtain ⟨ν, p, hp, rfl⟩ := (mem_nameAction_iff hρ π z).mp hz
  obtain ⟨hνD, hpP⟩ := kpair_mem_iff.mp (hb _ hp)
  obtain ⟨s, hs⟩ := mem_domain_iff.mp hνD
  exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem
    ((mem_nameAction_iff hτ π _).mpr ⟨ν, s, hs, rfl⟩), function_value_mem hπ.1 hpP⟩

theorem nameAction_bounded_iff {P R π ρ τ : V} (hπ : IsForcingAutomorphism P R π)
    (hρ : IsForcingName P ρ) (hτ : IsForcingName P τ) :
    nameAction π ρ ⊆ domain (nameAction π τ) ×ˢ P ↔ ρ ⊆ domain τ ×ˢ P := by
  constructor
  · intro hb
    have hh := nameAction_bounded (forcingAutomorphism_inverse hπ)
      (nameAction_isName hπ.1 hρ) (nameAction_isName hπ.1 hτ) hb
    simpa only [nameAction_inverse_cancel hπ hρ, nameAction_inverse_cancel hπ hτ] using hh
  · exact nameAction_bounded hπ hρ hτ

theorem hereditarilySymmetric_nameAction_iff {P R Γ F π τ : V}
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hF : IsNormalSubgroupFilter P Γ F)
    (hπ : π ∈ Γ) (hτ : IsForcingName P τ) :
    IsHereditarilySymmetricName P Γ F (nameAction π τ) ↔ IsHereditarilySymmetricName P Γ F τ := by
  constructor
  · intro hh
    have hi := hereditarilySymmetric_nameAction hΓ hF (hΓ.2.2.2 π hπ) hh
    simpa only [nameAction_inverse_cancel (hΓ.1 π hπ) hτ] using hi
  · exact hereditarilySymmetric_nameAction hΓ hF hπ

end ZFVP
